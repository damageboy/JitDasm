using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using LibObjectFile.Dwarf;
using LibObjectFile.Elf;

namespace JitDasm
{
    internal class ElfDumper
    {
        private readonly ElfObjectFile _elf;
        private readonly DisasmInfo[] _methods;
        private readonly SourceCodeProvider _sourceCodeProvider;

        internal ElfDumper(ElfObjectFile elf, DisasmInfo[] methods, SourceCodeProvider sourceCodeProvider)
        {
            _elf = elf;
            _methods = methods;
            _sourceCodeProvider = sourceCodeProvider;
        }
        public void DumpMethods()
        {
            var (codeSectionStartVA, codeSectionEndVA) = ExtractStartEndEnd();

            var codeSectionBytes = new byte[codeSectionEndVA - codeSectionStartVA];
            //Array.Fill(codeSectionBytes, (byte)0xCC);
            var codeMemory = new MemoryStream(codeSectionBytes);

            Debug.Assert(!_elf.Sections.Any(s => s.Type == ElfSectionType.ProgBits && s.Name == ".text"));

            var codeSection = _elf.AddSection(
                new ElfBinarySection(codeMemory) {VirtualAddress = codeSectionStartVA, Alignment = 4096}
                    .ConfigureAs(ElfSectionSpecialType.Text)
            );

            // Generate all symbols
            var syms =
                from method in _methods
                let startAddress = method.Code[0].IP
                let startOffset = startAddress - codeSectionStartVA
                select new ElfSymbol
                {
                    Name = method.MethodName,
                    Bind = ElfSymbolBind.Local,
                    Size = method.NativeCodeSize,
                    Type = ElfSymbolType.Function,
                    Section = codeSection,
                    Visibility = ElfSymbolVisibility.Default,
                    Value = startOffset,
                };
            var dumpedSymbols = syms.ToArray();

            // Dump the actual code bits to the code memory stream, methods-by-method,
            // instruction by instruction
            foreach (var method in _methods)
            {
                var startAddress = method.Code[0].IP;
                var startOffset = startAddress - codeSectionStartVA;

                foreach (var c in method.Code)
                {
                    Array.Copy(c.Code, 0, codeSectionBytes, (int) startOffset, c.Code.Length);
                    startOffset += (ulong) c.Code.LongLength;
                }
            }

            var stringSection = _elf.AddSection(new ElfStringTable());
            var symbolSection = _elf.AddSection(new ElfSymbolTable {Link = stringSection});
            symbolSection.Entries.AddRange(dumpedSymbols);
            _elf.AddSection(new ElfSectionHeaderStringTable());
            _elf.AddSegment(new ElfSegment()
            {
                Type = ElfSegmentTypeCore.Load,
                Range = codeSection,
                VirtualAddress = codeSectionStartVA,
                PhysicalAddress = codeSectionStartVA,
                Flags = ElfSegmentFlagsCore.Readable | ElfSegmentFlagsCore.Executable,
                Size = (ulong) codeSectionBytes.Length,
                SizeInMemory = (ulong) codeSectionBytes.Length,
                Alignment = 4096,
            });

            // Create DWARF Object
            var dwarfFile = new DwarfFile();


            var methodMap = new Dictionary<string, List<DisasmInfo>>();
            var fileMap = new Dictionary<string, DwarfFileName>();
            var linesMap = new Dictionary<string, List<DwarfLine>>();
            foreach (var method in _methods)
            {
                var il2native = method.ILMap.ToDictionary(x => x.ilOffset, x => x.nativeStartAddress);

                var statements =
                    _sourceCodeProvider.GetMethodStatementInfo(method).ToArray();
                
                if (statements.Length == 0)
                    continue;

                foreach (var f in statements.Select(s => s.DocumentUrl).Distinct())
                {
                    if (!fileMap.ContainsKey(f))
                        fileMap.Add(f, new DwarfFileName
                        {
                            Name = Path.GetFileName(f),
                            Directory = Path.GetDirectoryName(f),
                        });

                }

                foreach (var f in statements.Select(s => s.DocumentUrl).Distinct())
                {
                    if (!methodMap.TryGetValue(f, out var methodList))
                        methodMap.Add(f, new List<DisasmInfo> {method});
                    else
                        methodList.Add(method);
                }

                var dwarfLines =
                    from s in statements
                    let nativeAddress = il2native.ContainsKey(s.IlOffset) ? il2native[s.IlOffset] : 0UL
                    where nativeAddress != 0
                    select new DwarfLine
                    {
                        File = fileMap[s.DocumentUrl],
                        Address = nativeAddress - codeSectionStartVA,
                        Column = (uint) s.SeqPoint.StartColumn,
                        Line = (uint) s.SeqPoint.StartLine,
                    };

                var dwarfLineByFile =
                    from l in dwarfLines
                    group l by Path.Combine(l.File.Directory, l.File.Name)
                    into g
                    select (Filename: g.Key, Lines: g.ToList());

                foreach (var x in dwarfLineByFile)
                {
                    if (!linesMap.TryGetValue(x.Filename, out var lines))
                        linesMap.Add(x.Filename, x.Lines);
                    else
                        lines.AddRange(x.Lines);
                }
            }

            var sequenceMap = linesMap.ToDictionary(
                x => x.Key,
                x => GenerateLineSequnce(x.Value)
            );

            dwarfFile.LineTable.AddressSize = DwarfAddressSize.Bit64;

            foreach (var (filename, seq) in sequenceMap)
            {
                dwarfFile.LineTable.FileNames.Add(fileMap[filename]);
                dwarfFile.LineTable.AddLineSequence(seq);
            }

            var cus = new List<DwarfDIECompileUnit>();
            foreach (var fileName in fileMap.Values)
            {
                // Create .debug_info
                var cuDie = new DwarfDIECompileUnit
                {
                    Name = fileName.Name,
                    LowPC = 0, // 0 relative to base virtual address
                    HighPC = codeSectionBytes.Length, // default is offset/length after LowPC
                    CompDir = fileName.Directory,
                    Producer = "JitDasm",
                    StmtList = sequenceMap[Path.Combine(fileName.Directory, fileName.Name)],
                };

                foreach (var method in methodMap[Path.Combine(fileName.Directory, fileName.Name)])
                {
                    var subProgram = new DwarfDIESubprogram()
                    {
                        //Name = method.MethodFullName,
                        Name = method.MethodName,
                        LinkageName = method.MethodName,
                        LowPC = method.Code[0].IP - codeSectionStartVA,
                        HighPC = new DwarfConstant((int) method.NativeCodeSize),
                        DeclFile = fileName,
                        
                    };
                    cuDie.AddChild(subProgram);
                }

                cus.Add(cuDie);
            }

            var rootDieCu = cus[0];
            var lastCu = rootDieCu;
            foreach (var cuDie in cus.Skip(1))
            {
                lastCu.AddChild(cuDie);
                lastCu = cuDie;
            }

            var cu = new DwarfCompilationUnit()
            {
                AddressSize = DwarfAddressSize.Bit64,
                Root = rootDieCu
            };
            dwarfFile.InfoSection.AddUnit(cu);

            // AddressRange table
            dwarfFile.AddressRangeTable.AddressSize = DwarfAddressSize.Bit64;
            dwarfFile.AddressRangeTable.Unit = cu;
            dwarfFile.AddressRangeTable.Ranges.Add(new DwarfAddressRange(0, codeSectionStartVA, (ulong) codeSectionBytes.Length));

            // Transfer DWARF To ELF
            var dwarfElfContext = new DwarfElfContext(_elf);
            dwarfFile.WriteToElf(dwarfElfContext);

            (ulong codeSectionStartVA, ulong codeSectionEndVA) ExtractStartEndEnd()
            {
                var firstIP = _methods.Min(m => m.Code[0].IP);
                var lastIP = _methods.Max(m => m.Code[0].IP + m.NativeCodeSize);

                var codeSectionStartVa = (firstIP & ~0xFFFUL);
                var codeSectionEndVa = (lastIP & ~0xFFFUL) + 4096UL;
                return (codeSectionStartVa, codeSectionEndVa);
            }

            DwarfLineSequence GenerateLineSequnce(List<DwarfLine> lines)
            {
                var lineSeq = new DwarfLineSequence();
                lines.Sort(((l1, l2) => (int) ((long) l1.Address - (long) l2.Address)));
                foreach (var dl in lines)
                    lineSeq.Add(dl);
                return lineSeq;
            }

        }
    }
}

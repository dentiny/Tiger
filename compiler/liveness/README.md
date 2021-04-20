How to run type checker:
 - Compile and build SML parser:
       CM.make "sources.cm";
 - Parse the file you want:
       Parse.parse "*.tig";
 - Print the AST:
       PrintAbsyn.print(TextIO.stdOut, Parse.parse "*.tig");
 - Run the type checker & generate infinite-register MIPS assembly:
       Main.main "*.tig";

How to test thoroughly:
 - ./autotest.sh. All .s files will be generated.

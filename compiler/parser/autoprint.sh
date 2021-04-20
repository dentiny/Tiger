echo "CM.make \"sources.cm\";  PrintAbsyn.print(TextIO.stdOut, Parse.parse(\"../../testcases/queens.tig\"));" | sml > queens.out;
echo "CM.make \"sources.cm\";  PrintAbsyn.print(TextIO.stdOut, Parse.parse(\"../../testcases/merge.tig\"));" | sml > merge.out;
for i in {0..49}; do
    echo "CM.make \"sources.cm\";  PrintAbsyn.print(TextIO.stdOut, Parse.parse(\"../../testcases/test$i.tig\"));" | sml | sed '1,41d;$d' > res$i.out;
done
for i in {100..103}; do
    echo "CM.make \"sources.cm\";  PrintAbsyn.print(TextIO.stdOut, Parse.parse(\"../../testcases/test$i.tig\"));" | sml | sed '1,41d;$d' > res$i.out;
done
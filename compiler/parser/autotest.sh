echo "CM.make \"sources.cm\"; Parse.parse \"../../testcases/merge.tig\"; " | sml > merge.out;
echo "CM.make \"sources.cm\"; Parse.parse \"../../testcases/queens.tig\";" | sml > queens.out;
for i in {0..49}; do
    echo "CM.make \"sources.cm\"; Parse.parse \"../../testcases/test$i.tig\";" | sml | sed '1,39d;$d' > res$i.out;
done

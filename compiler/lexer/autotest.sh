# echo "CM.make \"sources.cm\"; Parse.parse \"../../testcases/merge.tig\"; " | sml > merge.out;
# echo "CM.make \"sources.cm\"; Parse.parse \"../../testcases/queens.tig\";" | sml > queens.out;
# for i in {0..49}; do
#     echo "CM.make \"sources.cm\"; Parse.parse \"../../testcases/test$i.tig\";" | sml | sed '1,25d' > res$i.out;
# done

# for filename in $(ls ../../testcases)
# do
#   echo "CM.make \"sources.cm\"; Parse.parse \"../../testcases/$filename.tig\";" | sml | sed '1,46d;$d' > $filename.out;
# done

for filename in $(ls ../../testcases)
do
  echo "CM.make \"sources.cm\"; Parse.parse \"../../testcases/$filename\";" | sml | sed '1,46d;$d' > $filename.out;
done
echo "The result of lexer has been generated in the current folder!"
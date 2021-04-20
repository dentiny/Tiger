for filename in $(ls ../../testcases)
do
  echo "CM.make \"sources.cm\"; Main.main \"../../testcases/$filename\";" | sml | sed '1,46d;$d' > $filename.out;
done

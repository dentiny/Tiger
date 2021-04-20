for filename in $(ls ../../testcases/*)
do
  echo $filename;
  echo "CM.make \"sources.cm\"; Main.compile \"$filename\";" | sml > /dev/null;
done
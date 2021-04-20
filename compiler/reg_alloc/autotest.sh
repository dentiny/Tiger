if [ -z "$1" ]; then

	# compile to .s
	echo "============ Compiling All tig files ==============="
	for filename in `ls ../../testcases/* | xargs -n 1 basename`
	do
		echo "CM.make \"sources.cm\"; Main.compile \"../../testcases/$filename\";" | sml  > "$filename".out;
		if [ -f "$filename".s ]; then
		  	cat regalloc/runtime.s regalloc/sysspim.s "$filename".s > "$filename".tmp.s;
		fi

	done

	echo "=========== Finished! Start running... ============="
	# running all generated .s
	for filename in `ls *.tmp.s`
	do
		echo "\nrunning:"$filename;
		if [[ $filename == "merge.tig.tmp.s" ]]; then
			echo "Sample input: 3 22 666;\n12 22 90;";
			echo "3 22 666;\n12 22 90;" | spim -file "$filename";
		#skip testcases that produce compile errors
		elif [ 	$filename == "test10.tig.tmp.s" \
				-o $filename == "test11.tig.tmp.s" \
				-o $filename == "test20.tig.tmp.s" \
				-o $filename == "test50.tig.tmp.s" \
				-o $filename == "testgroup1.tig.tmp.s" \
				-o $filename == "test19.tig.tmp.s" \
				-o $filename == "test24.tig.tmp.s" \
				-o $filename == "test8_11.tig.tmp.s" \
				-o $filename == "hj_queens.tig.tmp.s" \
				]; then
			echo "skipped:"$filename ;
		else
			spim -file "$filename" | sed '1,0d'; 
		fi
	done

	echo "====================== Done!! ======================="

else
	filename=$1;
	echo "CM.make \"sources.cm\"; Main.compile \"../../testcases/$filename\";" | sml  > "$filename".out;
	cat regalloc/runtime.s regalloc/sysspim.s "$filename".s > "$filename".tmp.s;

	spim -file "$filename".tmp.s;
fi
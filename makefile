all test.ml:
	echo ";;read_line();;" >> test.ml
	ocamlc -c test.mli
	ocamlmktop -o hi graphics.cma test.ml

coq:
	coqc graphicsTypeClass.v
	coqc graphics.v
	coqc pixelState.v
	coqc graphicsProofs.v




clean:
	-rm sample.cmi
	-rm sample.cmo
	-rm a.out
	-rm hi
	-rm test.cmi
	-rm test.cmo

coqclean:
	-rm *.vo
	-rm *.glob
	-rm *v.d

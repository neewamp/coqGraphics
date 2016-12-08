# all :
# 	ocamlc -i export.ml > export.mli
# 	ocamlc -c export.mli
# 	ocamlopt export.ml	If you need the mli file

all test.ml:
	echo ";;read_line();;" >> test.ml
	ocamlc -c test.mli
	ocamlc.opt -o hi graphics.cma test.ml

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

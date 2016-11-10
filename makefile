# all :
# 	ocamlc -i export.ml > export.mli
# 	ocamlc -c export.mli
# 	ocamlopt export.ml	If you need the mli file


all :
	ocamlmktop -o mine graphics.cma sample.ml

clean:
	rm sample.cmi
	rm sample.cmo
	rm mine

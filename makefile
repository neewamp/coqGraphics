all :
	ocamlc -i export.ml > export.mli
	ocamlopt export.ml

# all :
# 	ocamlc -i export.ml > export.mli
# 	ocamlc -c export.mli
# 	ocamlopt export.ml	If you need the mli file

HiDavid:
	ocamlc -i HiDavid.ml > HiDavid.mli
	ocamlc -c HiDavid.mli
	ocamlopt HiDavid.ml


all :
	ocamlmktop -o mine graphics.cma sample.ml

cleanHi:
	rm HiDavid.mli
	rm HiDavid.o

clean:
	rm sample.cmi
	rm sample.cmo
	rm mine

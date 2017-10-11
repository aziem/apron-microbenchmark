OCB_FLAGS = -use-ocamlfind
OCB = ocamlbuild $(OCB_FLAGS)

all: apronbenchmark.native

apronbenchmark.native: apronbenchmark.ml
	$(OCB) apronbenchmark.native

clean: 
	$(OCB) -clean 

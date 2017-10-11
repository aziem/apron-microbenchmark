OCB_FLAGS = -use-ocamlfind
OCB = ocamlbuild $(OCB_FLAGS)

all: mlbenchmark.native

mlbenchmark.native: mlbenchmark.ml
	$(OCB) mlbenchmark.native

clean: 
	$(OCB) -clean 

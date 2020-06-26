SOURCE_DIR = src
OCB = ocamlbuild
OCB_FLAGS = -use-ocamlfind -package 'gmp' -I $(SOURCE_DIR) 

all: top

top:
	$(OCB) $(OCB_FLAGS) poly.top

clean:
	$(OCB) -clean
	rm poly.top

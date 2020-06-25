SOURCE_DIR = src
OCB = ocamlbuild

all: top

top:
	$(OCB) -I $(SOURCE_DIR) poly.top

clean:
	$(OCB) -clean
	rm poly.top

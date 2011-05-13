CC = gcc
PICOSAT = ../Downloads/picosat-936
OCAML = /usr/local/lib/ocaml
CFLAGS = -I$(OCAML) -I$(PICOSAT)
OMT = ocamlmktop

all: picocaml.o
	$(OMT) -custom -o picocaml $(PICOSAT)/picosat.o $(PICOSAT)/version.o picocaml.o picocaml.ml

picocaml.o:
	$(CC) $(CFLAGS) -c picocaml.c

clean:
	rm *.cmi
	rm *.cmo
	rm *.o
	rm picocaml

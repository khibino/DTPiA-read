
gflag=--ghc-flag=-j2

all:
	agda -c $(gflag) HelloIO.agda
	agda -c $(gflag) Exercise4.agda

run:
	./HelloIO
	./runEx4.sh

clean:
	rm -fr MAlonzo
	find Ex4 \( -name '*.hi' -o -name '*.o' \) -print | xargs rm || true

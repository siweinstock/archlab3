llsim: llsim.c llsim.h sp.c
	gcc -Wall -o llsim -O2 llsim.c sp.c
clean:
	\rm llsim *~


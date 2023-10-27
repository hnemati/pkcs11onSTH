all: clean test

clean: 
	cd ../..; make clean

test:
	cd ../../guests/pkcs11/; make clean
	cd ../..; make
	./deploy.sh;
	./run.sh 

debug: 
	cd ../../guests/pkcs11; make clean
	cd ../..; make
	./deploy.sh;
	./run_debug.sh

all: init clean test

init:
	cd ../../; sed -i.bak "s/^SOFTWARE/#SOFTWARE/g" target
	cd ../../; sed -i.bak "s/^#SOFTWARE = linux/SOFTWARE = linux/g" target

clean:
	cd ../..; make clean

debug:
	cd ../..; make
	./deploy.sh
	./run.sh 1

test:
	cd ../..; make
	./deploy.sh;
	./run.sh 0


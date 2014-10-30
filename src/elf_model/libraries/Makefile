dummy: all

extract:
	mkdir batteries bitstring uint
	tar -zxvf batteries-2.2.tar.gz -C batteries --strip-components=1
	tar -zxvf bitstring.tar.gz -C bitstring --strip-components=1
	tar -zxvf uint.tar.gz -C uint --strip-components=1

clean:
	rm -rf batteries bitstring uint

make-batteries:
	make -C batteries all

make-uint:
	make -C uint configure
	make -C uint all

make-bitstring:
	cd bitstring && ./configure
	make -C bitstring

all: extract make-batteries make-bitstring make-uint
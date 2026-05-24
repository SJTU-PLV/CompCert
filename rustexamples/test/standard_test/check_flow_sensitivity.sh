#!/bin/zsh
# Note by czm: you should compile and install polonius from its git repository as its crates.io version is extremely outdated and not functional (at least on my machine).
rustc -Znll-facts -o /dev/null $1 > /dev/null 2>&1
FUNCS=$(find ./nll-facts -maxdepth 1 -mindepth 1)
FUNCS_CNT=$(echo $FUNCS | wc -l)
CORRECT_LINES=$(($FUNCS_CNT * 6))
NAIVE_LINES=$(echo $FUNCS | xargs -d '\n' polonius --show-tuples -a Naive | wc -l)
INSEN_LINES=$(echo $FUNCS | xargs -d '\n' polonius --show-tuples -a LocationInsensitive | wc -l)
if [[ $NAIVE_LINES != $CORRECT_LINES ]]; then
	echo "Incorrect example"
elif [[ $INSEN_LINES == $CORRECT_LINES ]]; then
	echo "Insensitive example"
else
	echo "Sensitive example"
fi
rm -rf ./nll-facts
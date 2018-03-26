mkdir ~/.agda && cd ~/.agda || exit 1

git clone https://github.com/agda/agda-stdlib.git

echo standard-library > defaults
echo "$HOME/.agda/agda-stdlib/standard-library.agda-lib" > libraries

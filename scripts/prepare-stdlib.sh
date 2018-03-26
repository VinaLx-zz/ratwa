mkdir ~/.agda && cd ~/.agda || exit 1

pwd

git clone https://github.com/agda/agda-stdlib.git

echo "$HOME/.agda/agda-stdlib/standard-library.agda-lib" > libraries


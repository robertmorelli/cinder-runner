docker build -t cinder-runner ./src
# FUCK YOU WINDOWS FUCK YOU FUCK YOU FUCK YOU
git config --global core.autocrlf false
git submodule update --init --recursive
docker run \
    -v "$PWD/vol:/vol" \
    -v "$PWD/rep:/home/trunner/rep"\
    -it cinder-runner


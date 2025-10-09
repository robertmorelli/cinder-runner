#!/usr/bin/env sh
set -e
cd ~/tests && git checkout main && git pull || echo 'unable to update repo'
cd ~
exec "$@"

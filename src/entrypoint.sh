#!/usr/bin/env sh
set -e
# run the setup
cd /vol && ./configure --enable-optimizations && make && echo 'done' || echo 'done but spicy'

exec "$@"

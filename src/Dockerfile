FROM ghcr.io/facebookincubator/cinder/python-build-env:latest

RUN echo 'root:password' | chpasswd

ARG TESTS_COMMIT=f9a611d6ecc416a704b9f09a24f287c8816d1a7f
ARG CINDER_COMMIT=1aeff3259dc0aa2f9d6e61623e73dcf0878ec38b

COPY installserver.sh /installserver.sh
RUN sed -i 's/\r$//' /installserver.sh && chmod +x /installserver.sh
COPY entrypoint.sh /entrypoint.sh
RUN sed -i 's/\r$//' /entrypoint.sh && chmod +x /entrypoint.sh
ENTRYPOINT ["/entrypoint.sh"]

RUN git clone --no-checkout https://github.com/facebookincubator/cinder /vol \
 && cd /vol \
 && git fetch --depth=1 --no-tags origin "$CINDER_COMMIT" \
 && git checkout --detach "$CINDER_COMMIT" \
 && git submodule update --init --recursive --depth=1 \
 && ./configure --enable-optimizations \
 && make -j"$(nproc)"

RUN useradd -m -s /bin/bash trunner \
 && chown -R trunner:trunner /home/trunner
USER trunner
WORKDIR /home/trunner

RUN git clone --no-checkout https://github.com/utahplt/static-python-perf /home/trunner/tests \
 && cd /home/trunner/tests \
 && git fetch --depth=1 --no-tags origin "$TESTS_COMMIT" \
 && git checkout --detach "$TESTS_COMMIT"

ENV PYTHONINSTALLSTRICTLOADER=1
CMD ["bash"]

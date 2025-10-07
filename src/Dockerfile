FROM ghcr.io/facebookincubator/cinder/python-build-env:latest

RUN useradd -m -s /bin/bash trunner \
    && mkdir -p /vol \
    && chown -R trunner:trunner /home/trunner

COPY entrypoint.sh /entrypoint.sh
RUN sed -i 's/\r$//' /entrypoint.sh && chmod +x /entrypoint.sh

USER trunner
WORKDIR /home/trunner

ENTRYPOINT ["/entrypoint.sh"]
CMD ["bash"]

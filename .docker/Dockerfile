# This Dockerfile mostly exists to verify that the Makefile works;
# it's unlikely that we'll actually use it "in production"!
# You may also need to allow the Docker engine a lot of memory (32gb?)
FROM ubuntu

USER root

# Set timezone to UTC to avoid prompts from tzdata.
RUN TZ=UTC ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone
# Install prerequisites.
RUN apt-get update && \
    apt-get install -y git libgmp-dev cmake ccache clang && \
    apt-get install -y curl python3-yaml python3 python-is-python3 && \
    apt-get clean

# create a non-root user
RUN useradd -m lean

USER lean
WORKDIR /home/lean

SHELL ["/bin/bash", "-c"]
# set the entrypoint to be a login shell, so everything is on the PATH
ENTRYPOINT ["/bin/bash", "-l"]

# make sure binaries are available even in non-login shells
ENV PATH="/home/lean/.elan/bin:/home/lean/.local/bin:$PATH"

# install elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y && \
    . ~/.profile && \
    elan toolchain uninstall stable

RUN git clone https://github.com/leanprover-community/mathport
WORKDIR /home/lean/mathport

RUN make build
RUN make mathbin-source
RUN make lean3-source
RUN make lean3-predata
RUN make port-lean
RUN make mathbin-predata
RUN make port-mathbin
RUN make test-import-leanbin
RUN make test-import-mathbin

FROM nvidia/cuda:12.4.1-cudnn-devel-ubuntu22.04

SHELL ["/bin/bash", "-c"]

RUN set -eux; \
    apt-get update; \
    apt-get install -y --no-install-recommends \
    ca-certificates \
    # ERROR: no download agent available; install curl, wget, or fetch
    curl \
    build-essential \
    git \
    zsh \
    vim \
    ; \
    rm -rf /var/lib/apt/lists/*

RUN sh -c "$(curl -fsSL https://raw.githubusercontent.com/ohmyzsh/ohmyzsh/master/tools/install.sh)"

SHELL ["/bin/zsh", "-c"]

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

RUN curl -fsSL https://install.julialang.org | sh -s -- -y

# RUN cat /root/.bashrc
# RUN source /root/.bashrc

ENV JULIA_PATH=/root/.juliaup
ENV CARGO_PATH=/root/.cargo
ENV PATH=$JULIA_PATH/bin:$CARGO_PATH/bin:$PATH

RUN juliaup add 1.11.0
RUN juliaup default 1.11.0

RUN julia -e 'using Pkg; Pkg.add(["Revise", "TestEnv", "OhMyREPL", "TerminalExtensions"])'

RUN mkdir -p /root/.julia/config
RUN echo 'atreplinit((_)->Base.require(Main, :TerminalExtensions))' > /root/.julia/config/startup.jl
RUN echo 'using Revise' >> /root/.julia/config/startup.jl
RUN echo 'using OhMyREPL' >> /root/.julia/config/startup.jl
RUN echo 'using TestEnv' >> /root/.julia/config/startup.jl

COPY . /workspaces/expcoder

RUN cd /workspaces/expcoder && git remote set-url origin git@github.com:andreyz4k/expcoder.git

RUN julia --project=/workspaces/expcoder -e 'using Pkg; Pkg.instantiate(); using Revise; using solver'

LABEL org.opencontainers.image.source=https://github.com/andreyz4k/expcoder

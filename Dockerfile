FROM ubuntu:22.04

# set noninteractive installation
ENV DEBIAN_FRONTEND=noninteractive

# set timezone
RUN ln -fs /usr/share/zoneinfo/Etc/UTC /etc/localtime && echo "Etc/UTC" > /etc/timezone

ENV USER=ubuntu
ENV PASSWD=craneirgen
ENV WORKDIR=CraneIRGen

# set apt mirror to tsinghua
RUN printf '\n\
deb http://mirrors.tuna.tsinghua.edu.cn/ubuntu/ jammy main restricted universe multiverse \n\
deb http://mirrors.tuna.tsinghua.edu.cn/ubuntu/ jammy-updates main restricted universe multiverse \n\
deb http://mirrors.tuna.tsinghua.edu.cn/ubuntu/ jammy-backports main restricted universe multiverse \n\
deb http://mirrors.tuna.tsinghua.edu.cn/ubuntu/ jammy-security main restricted universe multiverse' > /etc/apt/sources.list


# install packages
RUN apt-get update \
  && apt-get install -y ssh openssh-server build-essential \
    gcc g++ gdb gdbserver cmake \
    libboost-dev \
    net-tools tar rsync \
    gnupg curl\
    bash-completion \
    python3 python3-pip \
    sudo git\
  && apt-get clean \
  && python3 -m pip install --upgrade pip \
  && pip config set global.index-url https://pypi.tuna.tsinghua.edu.cn/simple

# set bash as default shell
SHELL ["/bin/bash", "-c"]
RUN source /root/.bashrc

# install mongodb
RUN curl -fsSL https://www.mongodb.org/static/pgp/server-7.0.asc | \
sudo gpg -o /usr/share/keyrings/mongodb-server-7.0.gpg \
--dearmor

# install rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

RUN echo "deb [ arch=amd64,arm64 signed-by=/usr/share/keyrings/mongodb-server-7.0.gpg ] https://repo.mongodb.org/apt/ubuntu jammy/mongodb-org/7.0 multiverse" | sudo tee /etc/apt/sources.list.d/mongodb-org-7.0.list

RUN sudo apt-get update \
  && sudo apt-get install -y mongodb-org


RUN useradd -m ${USER} && yes ${PASSWD} | passwd ${USER}

# set sudo
RUN echo ${USER}' ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers
RUN chmod 644 /etc/sudoers

# make workdir and binaries output dir
RUN mkdir -p /home/${USER}/${WORKDIR}/
COPY mongodb_ir /home/${USER}/mongodb_ir



COPY start.sh /start.sh
RUN chmod +x /start.sh
CMD ["/start.sh"]


COPY . /home/${USER}/${WORKDIR}/


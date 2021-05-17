FROM ubuntu
RUN apt-get update
RUN apt-get upgrade -y
RUN DEBIAN_FRONTEND="noninteractive" apt-get install -y opam build-essential libgmp-dev z3 pkg-config zlib1g-dev
RUN mkdir /etc/sudoers.d/ && \
  echo 'opam ALL=(ALL:ALL) NOPASSWD:ALL' > /etc/sudoers.d/opam && \
  chmod 440 /etc/sudoers.d/opam && \
  chown root:root /etc/sudoers.d/opam && \
  adduser --disabled-password --gecos '' opam && \
  passwd -l opam && \
  chown -R opam:opam /home/opam
USER opam
ENV HOME /home/opam
WORKDIR /home/opam
RUN opam init --disable-sandboxing
RUN eval `opam env` && \
  opam repository add rems https://github.com/rems-project/opam-repository.git && \
  opam install -y sail
COPY --chown=opam docker_entry_point.sh /home/opam/
RUN chmod +x docker_entry_point.sh
WORKDIR /data
ENTRYPOINT ["/home/opam/docker_entry_point.sh"]

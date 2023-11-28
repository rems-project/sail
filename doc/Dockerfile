FROM debian

RUN apt-get update && apt-get install -y --no-install-recommends build-essential git ruby ruby-rubygems opam z3 rsync libgmp-dev pkg-config zlib1g-dev texlive-latex-base texlive-pictures poppler-utils

RUN gem install asciidoctor asciidoctor-pdf asciidoctor-bibtex asciidoctor-sail rouge

RUN opam init -y --no-setup --compiler=5.1.0 --shell=sh --disable-sandboxing; eval "$(opam env)"; opam install -y obelisk

WORKDIR /sail
COPY . /sail

RUN eval "$(opam env)"; opam install -y .; make -B asciidoc

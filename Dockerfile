FROM ocaml/opam:ubuntu

RUN sudo apt update
RUN sudo apt install -y gcc-multilib utop tmux

RUN opam pin add GT https://github.com/dboulytchev/GT.git -y
RUN opam pin add ostap https://github.com/dboulytchev/ostap.git -y
RUN opam install -y GT
RUN opam install -y ostap



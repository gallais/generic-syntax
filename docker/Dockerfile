FROM haskell:8
RUN stack install Agda-2.5.4
RUN apt-get update && apt-get install -y wget 
RUN wget https://github.com/agda/agda-stdlib/archive/v0.16.tar.gz
RUN mkdir .agda
RUN tar -xzvf v0.16.tar.gz -C .agda/
RUN echo "/.agda/agda-stdlib-0.16/standard-library.agda-lib" > .agda/libraries-2.5.4
ENV AGDA_DIR /.agda
RUN git clone https://github.com/gallais/generic-syntax --depth=1
CMD cd generic-syntax/src && agda --ignore-interfaces TableOfContent.agda

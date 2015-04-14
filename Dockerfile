FROM quay.io/crypto_agda/agda
RUN apt-get update && apt-get install -y git
RUN git  clone https://github.com/np/agda-pkg &&\
    cp agda-pkg/agda-pkg /usr/local/bin/agda-pkg &&\
    agda-pkg -pagda/agda-stdlib#2.4.2.3 \
             -pnp/agda-parametricity \
             -pcrypto-agda/agda-nplib \
             -pcrypto-agda/agda-libjs \
             -pcrypto-agda/explore \
             -pcrypto-agda/protocols -n
ADD . /app/
WORKDIR /app
RUN agda-pkg -cagda-pkg.conf --html crypto-agda.agda
RUN apt-get update && apt-get install -y nodejs npm
RUN apt-get install -y coffeescript node-request
RUN npm install sha256
RUN ln -s /usr/bin/nodejs /usr/local/bin/node
RUN npm install requirejs bigi sha1
RUN ./runjs.sh

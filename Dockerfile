FROM ghcr.io/puppeteer/puppeteer:22.0.0

WORKDIR /app

COPY package.json ./
RUN npm install

COPY . .

CMD ["node", "server.js"]

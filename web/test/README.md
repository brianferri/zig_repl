# web/test

Headless browser checks for the wasm SPA in `../public`, in TypeScript

The harness drives a *served* page, so build and serve the frontend first:

    zig build wasm                # repo root -> zig-out/web
    npx serve zig-out/web         # any static server on :3000

Then, from this directory:

    npm install                   # first time
    npm test                      # drives http://localhost:3000 (BASE_URL overrides)
    npm run check                 # typecheck tests + ../public (checkJs) + eslint

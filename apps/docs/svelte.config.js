import adapter from "@sveltejs/adapter-static";
import { vitePreprocess } from "@sveltejs/vite-plugin-svelte";

const base = process.env.BASE_PATH ?? "";

export default {
  preprocess: vitePreprocess(),
  kit: {
    adapter: adapter({
      fallback: "404.html",
      pages: process.env.DOCS_OUT_DIR ?? "build",
      assets: process.env.DOCS_OUT_DIR ?? "build",
    }),
    paths: { base },
    // API and Lean docs are copied into the output by CI after Svelte builds.
    prerender: {
      handleHttpError: ({ path, message }) => {
        const sitePath = path.slice(base.length);
        if (sitePath.startsWith("/api/") || sitePath.startsWith("/lean/"))
          return;
        throw new Error(message);
      },
    },
  },
};

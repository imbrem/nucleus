import adapter from "@sveltejs/adapter-static";
import { vitePreprocess } from "@sveltejs/vite-plugin-svelte";

export default {
  preprocess: vitePreprocess(),
  kit: {
    adapter: adapter({
      fallback: "404.html",
      pages: process.env.DOCS_OUT_DIR ?? "build",
      assets: process.env.DOCS_OUT_DIR ?? "build",
    }),
    paths: { base: process.env.BASE_PATH ?? "" },
    prerender: { handleHttpError: "warn" },
  },
};

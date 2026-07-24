import { sveltekit } from "@sveltejs/kit/vite";
import { defineConfig } from "vite";
import { buildMetadata } from "./build-metadata";

export default defineConfig({
  define: { __BUILD_METADATA__: JSON.stringify(buildMetadata()) },
  plugins: [sveltekit()],
});

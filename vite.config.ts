import { sveltekit } from '@sveltejs/kit/vite';
import { defineConfig } from 'vite';
// FIXME: this
// @ts-ignore
import rust from "@wasm-tool/rollup-plugin-rust";

export default defineConfig({
	plugins: [
		rust({
			verbose: true,
			serverPath: 'build/'
		}),
		sveltekit()
	],
	build: {
		rollupOptions: {
			plugins: [
				rust({
					verbose: true,
					serverPath: 'build/'
				})
			]
		}
	},
});

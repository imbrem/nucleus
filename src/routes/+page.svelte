<script>
	import { onMount } from 'svelte';
	//TODO: actually fix this using https://github.com/wasm-tool/rollup-plugin-rust/issues/9
	// @ts-ignore
	import wasm from '../../nucleus/nucleus-wasm/Cargo.toml';
	import CodeMirror from 'svelte-codemirror-editor';

	async function getBindings() {
		return await wasm();
	}

	let value = $state('');

	// @ts-ignore
	let dlcf = $state(null);

	// @ts-ignore
	let result = $derived(dlcf ? dlcf.handle_input(value) : null);

	onMount(async () => {
		dlcf = new (await getBindings()).WebNucleus();
	});
</script>

<div class="window">
	<div class="editor">
		<CodeMirror bind:value nodebounce />
	</div>
	<div class="pane">
		{#if dlcf}
			<ul class="ctx">
				<li><code>Result: {result}</code></li>
			</ul>
		{:else}
			<p>Loading WebDLCF...</p>
		{/if}
	</div>
</div>

<style>
	.window {
		display: flex;
		flex-direction: left;
	}

	.editor {
		width: 50%;
	}

    .pane {
        max-width: 50%;
    }

    .ctx {
        list-style-type: none;
    }
</style>
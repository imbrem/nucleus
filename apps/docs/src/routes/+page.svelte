<script lang="ts">
  import { base } from '$app/paths';
  import DependencyGraph from '$lib/DependencyGraph.svelte';
  import '../app.css';
</script>

<svelte:head><title>Nucleus</title></svelte:head>

<main>
  <header class="hero">
    <p class="eyebrow">Covalence trusted core</p>
    <h1>Nucleus<span>.</span></h1>
    <p class="lede">A portable, auditable foundation for a theorem-proving system.</p>
  </header>
  <DependencyGraph />
  <footer>
    <dl>
    <dt>source</dt><dd>{__BUILD_METADATA__.commit}{__BUILD_METADATA__.dirty ? ' (dirty)' : ''}</dd>
    <dt>built</dt><dd>{__BUILD_METADATA__.builtAt}</dd>
    <dt>rust</dt><dd>{__BUILD_METADATA__.rust}</dd>
    <dt>glu</dt><dd>{__BUILD_METADATA__.glu}</dd>
    </dl>
    <a href={`${base}/api/nucleus/`}>Browse Rust API documentation →</a>
  </footer>
</main>

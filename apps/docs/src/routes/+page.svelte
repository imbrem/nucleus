<script lang="ts">
  import { base } from "$app/paths";
  import DependencyGraph from "$lib/DependencyGraph.svelte";
</script>

<svelte:head><title>Nucleus</title></svelte:head>

<main>
  <DependencyGraph />
  <footer>
    <dl>
      <dt>source</dt>
      <dd>
        {__BUILD_METADATA__.commit}{__BUILD_METADATA__.dirty ? " (dirty)" : ""}
      </dd>
      <dt>built</dt>
      <dd>{__BUILD_METADATA__.builtAt}</dd>
      <dt>rust</dt>
      <dd>{__BUILD_METADATA__.rust}</dd>
      <dt>glu</dt>
      <dd>{__BUILD_METADATA__.glu}</dd>
    </dl>
    <a href={`${base}/api/nucleus/`}>Browse Rust API documentation →</a>
  </footer>
</main>

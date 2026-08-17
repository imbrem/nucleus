<script lang="ts">
  import { base } from "$app/paths";
  import "../app.css";

  let { children } = $props();
</script>

<nav class="site-nav" aria-label="Primary navigation">
  <a href={`${base}/`}>Status</a>
  <a href={`${base}/crates/`}>Crates</a>
  <a href={`${base}/dependencies/`}>Dependencies</a>
  <a href={`${base}/notes/`}>Notes</a>
  <a href={`${base}/api/nucleus/`}>API</a>
  <a href={`${base}/lean/Nucleus/`}>Lean</a>
</nav>

{@render children()}

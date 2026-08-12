<script lang="ts">
  import { base } from "$app/paths";
  import "../app.css";

  let { children } = $props();
</script>

<header class="site-header">
  <nav class="site-nav" aria-label="Primary navigation">
    <a class="wordmark" href={`${base}/`} aria-label="Nucleus home">
      <span aria-hidden="true">nucleus&gt;</span>
    </a>
    <div class="site-links">
      <a href={`${base}/`}>Status</a>
      <a href={`${base}/crates/`}>Crates</a>
      <a href={`${base}/dependencies/`}>Dependencies</a>
      <a href={`${base}/api/nucleus/`}>Rust API</a>
      <a href={`${base}/lean/Nucleus/`}>Lean</a>
      <a class="repl-link" href={`${base}/repl/`}>Open REPL <span>↗</span></a>
    </div>
  </nav>
</header>

{@render children()}

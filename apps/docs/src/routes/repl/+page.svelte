<script lang="ts">
  import { base } from "$app/paths";
</script>

<svelte:head>
  <title>Browser REPL · Nucleus</title>
  <meta
    name="description"
    content="Run the Nucleus REPL and immutable SQLite shell in the browser."
  />
</svelte:head>

<main class="repl-page">
  <section class="repl-intro" aria-labelledby="repl-heading">
    <div>
      <p class="eyebrow">Live static demo</p>
      <h1 id="repl-heading">A kernel in the page.</h1>
    </div>
    <p>
      The REPL, local CAS, and SQLite shell run locally in WebAssembly. Try the
      bundled databases without installing anything or trusting the shell.
    </p>
  </section>

  <div class="repl-frame">
    <div class="repl-frame-bar" aria-hidden="true">
      <span></span><span></span><span></span>
      <strong>nucleus / browser</strong>
    </div>
    <iframe
      src={`${base}/repl-app/demo.html`}
      title="Interactive Nucleus browser REPL"
    ></iframe>
  </div>

  <p class="repl-note">
    This static build includes the local kernel and demo databases. Remote CAS
    and SAT providers remain ordinary host integrations when the full demo
    server is running.
  </p>
</main>

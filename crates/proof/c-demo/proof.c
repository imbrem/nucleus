// Minimal C implementation of the asynchronous Nucleus proof component ABI.
//
// The component is untrusted. It can only return a checked kernel resource
// created by the host, so this language boundary does not enlarge the TCB.

#include "proof.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static const uint8_t DEFAULT_INPUT[32] = {
    0x02, 0xc4, 0xf6, 0x10, 0xbb, 0x41, 0xad, 0x65,
    0x2b, 0xf8, 0x7d, 0x0d, 0xba, 0x85, 0x83, 0xd8,
    0x99, 0xd0, 0x94, 0x79, 0xef, 0x66, 0x32, 0x86,
    0xf3, 0xb3, 0xa1, 0x61, 0xc2, 0x2c, 0x09, 0xcf,
};

static const uint8_t EXPECTED_INPUT[] = "nucleus proof demo";

struct proof_task {
  enum {
    PROOF_ENTRY_ADDR,
    PROOF_ENTRY_NAME,
    PROOF_ENTRY_IX,
    PROOF_ENTRY_BYTES,
  } entry;
  uint8_t address[32];
  exports_nucleus_proof_standard_own_kernel_t kernel;
  nucleus_proof_host_result_option_own_bytes_string_t fetch;
  proof_subtask_t subtask;
  proof_waitable_set_t wait_set;
};

static void return_result(
    int entry, exports_nucleus_proof_standard_result_own_kernel_string_t result) {
  switch (entry) {
  case PROOF_ENTRY_ADDR:
    exports_nucleus_proof_standard_prove_addr_return(result);
    break;
  case PROOF_ENTRY_NAME:
    exports_nucleus_proof_standard_prove_name_return(result);
    break;
  case PROOF_ENTRY_IX:
    exports_nucleus_proof_standard_prove_ix_return(result);
    break;
  case PROOF_ENTRY_BYTES:
    exports_nucleus_proof_standard_prove_bytes_return(result);
    break;
  }
}

static void return_error(int entry, const char *message) {
  exports_nucleus_proof_standard_result_own_kernel_string_t result = {
      .is_err = true,
  };
  proof_string_dup(&result.val.err, message);
  return_result(entry, result);
}

static proof_callback_code_t return_task_error(struct proof_task *task,
                                               const char *message) {
  nucleus_proof_host_kernel_drop_own(task->kernel);
  int entry = task->entry;
  free(task);
  return_error(entry, message);
  return PROOF_CALLBACK_CODE_EXIT;
}

static proof_callback_code_t finish_fetch(struct proof_task *task) {
  if (task->fetch.is_err) {
    nucleus_proof_host_result_option_own_bytes_string_free(&task->fetch);
    return return_task_error(task, "the asynchronous CAS fetch failed");
  }
  if (!task->fetch.val.ok.is_some) {
    nucleus_proof_host_result_option_own_bytes_string_free(&task->fetch);
    return return_task_error(task, "proof input is absent from the default CAS");
  }

  nucleus_proof_host_own_bytes_t bytes = task->fetch.val.ok.val;
  proof_list_u8_t value = {0};
  nucleus_proof_host_method_bytes_to_list(
      nucleus_proof_host_borrow_bytes(bytes), &value);
  bool matches = value.len == sizeof(EXPECTED_INPUT) - 1 &&
                 memcmp(value.ptr, EXPECTED_INPUT, value.len) == 0;
  proof_list_u8_free(&value);
  nucleus_proof_host_result_option_own_bytes_string_free(&task->fetch);

  if (!matches) {
    return return_task_error(task, "async CAS fetch changed the proof input");
  }

  exports_nucleus_proof_standard_result_own_kernel_string_t result = {
      .is_err = false,
      .val.ok = task->kernel,
  };
  return_result(task->entry, result);
  free(task);
  return PROOF_CALLBACK_CODE_EXIT;
}

static proof_callback_code_t start_proof(
    int entry, const uint8_t *address_bytes, size_t address_len,
    exports_nucleus_proof_standard_own_kernel_t kernel) {
  if (address_len != 32) {
    nucleus_proof_host_kernel_drop_own(kernel);
    return_error(entry, "proof addresses must contain 32 bytes");
    return PROOF_CALLBACK_CODE_EXIT;
  }

  struct proof_task *task = calloc(1, sizeof(struct proof_task));
  if (task == NULL) {
    nucleus_proof_host_kernel_drop_own(kernel);
    return_error(entry, "could not allocate the C proof task");
    return PROOF_CALLBACK_CODE_EXIT;
  }
  task->entry = entry;
  task->kernel = kernel;

  bool default_name = true;
  for (size_t index = 0; index < address_len; ++index) {
    default_name = default_name && address_bytes[index] == 0;
  }
  memcpy(task->address, default_name ? DEFAULT_INPUT : address_bytes,
         sizeof(task->address));

  proof_list_u8_t wire_address = {
      .ptr = task->address,
      .len = sizeof(task->address),
  };
  proof_subtask_status_t status =
      nucleus_proof_host_cas_get_bytes(wire_address, &task->fetch);
  switch (PROOF_SUBTASK_STATE(status)) {
  case PROOF_SUBTASK_RETURNED:
    return finish_fetch(task);
  case PROOF_SUBTASK_STARTING:
  case PROOF_SUBTASK_STARTED:
    task->subtask = PROOF_SUBTASK_HANDLE(status);
    task->wait_set = proof_waitable_set_new();
    proof_waitable_join(task->subtask, task->wait_set);
    proof_context_set_0(task);
    return PROOF_CALLBACK_CODE_WAIT(task->wait_set);
  default:
    return return_task_error(
        task, "the asynchronous CAS fetch was cancelled while starting");
  }
}

proof_callback_code_t exports_nucleus_proof_standard_prove_addr(
    proof_list_u8_t *addr,
    exports_nucleus_proof_standard_own_kernel_t kernel) {
  return start_proof(PROOF_ENTRY_ADDR, addr->ptr, addr->len, kernel);
}

proof_callback_code_t exports_nucleus_proof_standard_prove_name(
    proof_string_t *name,
    exports_nucleus_proof_standard_own_kernel_t kernel) {
  if (name->len != 7 || memcmp(name->ptr, "default", 7) != 0) {
    nucleus_proof_host_kernel_drop_own(kernel);
    return_error(PROOF_ENTRY_NAME, "the C demo accepts the name `default` only");
    return PROOF_CALLBACK_CODE_EXIT;
  }
  return start_proof(PROOF_ENTRY_NAME, DEFAULT_INPUT, sizeof(DEFAULT_INPUT), kernel);
}

proof_callback_code_t exports_nucleus_proof_standard_prove_ix(
    uint64_t ix, exports_nucleus_proof_standard_own_kernel_t kernel) {
  if (ix != 0) {
    nucleus_proof_host_kernel_drop_own(kernel);
    return_error(PROOF_ENTRY_IX, "the C demo accepts proof index zero only");
    return PROOF_CALLBACK_CODE_EXIT;
  }
  return start_proof(PROOF_ENTRY_IX, DEFAULT_INPUT, sizeof(DEFAULT_INPUT), kernel);
}

proof_callback_code_t exports_nucleus_proof_standard_prove_bytes(
    exports_nucleus_proof_standard_own_bytes_t bytes,
    exports_nucleus_proof_standard_own_kernel_t kernel) {
  proof_list_u8_t value = {0};
  nucleus_proof_host_method_bytes_to_list(
      nucleus_proof_host_borrow_bytes(bytes), &value);
  bool is_default = value.len == 7 && memcmp(value.ptr, "default", 7) == 0;
  proof_list_u8_free(&value);
  nucleus_proof_host_bytes_drop_own(bytes);
  if (!is_default) {
    nucleus_proof_host_kernel_drop_own(kernel);
    return_error(PROOF_ENTRY_BYTES,
                 "the C demo accepts the bytes `default` only");
    return PROOF_CALLBACK_CODE_EXIT;
  }
  return start_proof(PROOF_ENTRY_BYTES, DEFAULT_INPUT, sizeof(DEFAULT_INPUT), kernel);
}

static proof_callback_code_t resume_proof(proof_event_t *event, int entry) {
  struct proof_task *task = proof_context_get_0();
  proof_context_set_0(NULL);
  if (task == NULL) {
    return_error(entry, "the C proof callback lost its task context");
    return PROOF_CALLBACK_CODE_EXIT;
  }

  proof_waitable_join(task->subtask, 0);
  if (event->event == PROOF_EVENT_CANCEL) {
    proof_subtask_cancel(task->subtask);
    proof_subtask_drop(task->subtask);
    proof_waitable_set_drop(task->wait_set);
    nucleus_proof_host_kernel_drop_own(task->kernel);
    free(task);
    proof_task_cancel();
    return PROOF_CALLBACK_CODE_EXIT;
  }

  if (event->event != PROOF_EVENT_SUBTASK ||
      event->waitable != task->subtask ||
      PROOF_SUBTASK_STATE(event->code) !=
          PROOF_SUBTASK_RETURNED) {
    proof_subtask_drop(task->subtask);
    proof_waitable_set_drop(task->wait_set);
    return return_task_error(task,
                             "the C proof received an unexpected async event");
  }

  proof_subtask_drop(task->subtask);
  proof_waitable_set_drop(task->wait_set);
  return finish_fetch(task);
}


proof_callback_code_t exports_nucleus_proof_standard_prove_addr_callback(
    proof_event_t *event) {
  return resume_proof(event, PROOF_ENTRY_ADDR);
}

proof_callback_code_t exports_nucleus_proof_standard_prove_name_callback(
    proof_event_t *event) {
  return resume_proof(event, PROOF_ENTRY_NAME);
}

proof_callback_code_t exports_nucleus_proof_standard_prove_ix_callback(
    proof_event_t *event) {
  return resume_proof(event, PROOF_ENTRY_IX);
}

proof_callback_code_t exports_nucleus_proof_standard_prove_bytes_callback(
    proof_event_t *event) {
  return resume_proof(event, PROOF_ENTRY_BYTES);
}

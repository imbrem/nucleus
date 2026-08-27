// Minimal C implementation of the asynchronous Nucleus proof component ABI.
//
// The component is untrusted. It can only return a checked kernel resource
// created by the host, so this language boundary does not enlarge the TCB.

#include "standard_proof.h"

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
  uint8_t address[32];
  nucleus_proof_host_result_option_own_bytes_string_t fetch;
  standard_proof_subtask_t subtask;
  standard_proof_waitable_set_t wait_set;
};

static void return_error(const char *message) {
  exports_nucleus_proof_standard_result_own_kernel_string_t result = {
      .is_err = true,
  };
  standard_proof_string_dup(&result.val.err, message);
  exports_nucleus_proof_standard_prove_return(result);
}

static standard_proof_callback_code_t finish_fetch(struct proof_task *task) {
  if (task->fetch.is_err) {
    nucleus_proof_host_result_option_own_bytes_string_free(&task->fetch);
    return_error("the asynchronous CAS fetch failed");
    free(task);
    return STANDARD_PROOF_CALLBACK_CODE_EXIT;
  }
  if (!task->fetch.val.ok.is_some) {
    nucleus_proof_host_result_option_own_bytes_string_free(&task->fetch);
    return_error("proof input is absent from the default CAS");
    free(task);
    return STANDARD_PROOF_CALLBACK_CODE_EXIT;
  }

  nucleus_proof_host_own_bytes_t bytes = task->fetch.val.ok.val;
  standard_proof_list_u8_t value = {0};
  nucleus_proof_host_method_bytes_to_list(
      nucleus_proof_host_borrow_bytes(bytes), &value);
  bool matches = value.len == sizeof(EXPECTED_INPUT) - 1 &&
                 memcmp(value.ptr, EXPECTED_INPUT, value.len) == 0;
  standard_proof_list_u8_free(&value);
  nucleus_proof_host_result_option_own_bytes_string_free(&task->fetch);

  if (!matches) {
    return_error("async CAS fetch changed the proof input");
    free(task);
    return STANDARD_PROOF_CALLBACK_CODE_EXIT;
  }

  exports_nucleus_proof_standard_result_own_kernel_string_t result = {
      .is_err = false,
      .val.ok = nucleus_proof_host_constructor_kernel(),
  };
  exports_nucleus_proof_standard_prove_return(result);
  free(task);
  return STANDARD_PROOF_CALLBACK_CODE_EXIT;
}

standard_proof_callback_code_t exports_nucleus_proof_standard_prove(
    standard_proof_list_u8_t *target) {
  if (target->len != 32) {
    return_error("proof targets must contain 32 bytes");
    return STANDARD_PROOF_CALLBACK_CODE_EXIT;
  }

  struct proof_task *task = calloc(1, sizeof(struct proof_task));
  if (task == NULL) {
    return_error("could not allocate the C proof task");
    return STANDARD_PROOF_CALLBACK_CODE_EXIT;
  }

  bool default_target = true;
  for (size_t index = 0; index < target->len; ++index) {
    default_target = default_target && target->ptr[index] == 0;
  }
  memcpy(task->address, default_target ? DEFAULT_INPUT : target->ptr,
         sizeof(task->address));

  standard_proof_list_u8_t address = {
      .ptr = task->address,
      .len = sizeof(task->address),
  };
  standard_proof_subtask_status_t status =
      nucleus_proof_host_cas_get_bytes(address, &task->fetch);
  switch (STANDARD_PROOF_SUBTASK_STATE(status)) {
  case STANDARD_PROOF_SUBTASK_RETURNED:
    return finish_fetch(task);
  case STANDARD_PROOF_SUBTASK_STARTING:
  case STANDARD_PROOF_SUBTASK_STARTED:
    task->subtask = STANDARD_PROOF_SUBTASK_HANDLE(status);
    task->wait_set = standard_proof_waitable_set_new();
    standard_proof_waitable_join(task->subtask, task->wait_set);
    standard_proof_context_set_0(task);
    return STANDARD_PROOF_CALLBACK_CODE_WAIT(task->wait_set);
  default:
    free(task);
    return_error("the asynchronous CAS fetch was cancelled while starting");
    return STANDARD_PROOF_CALLBACK_CODE_EXIT;
  }
}

standard_proof_callback_code_t exports_nucleus_proof_standard_prove_callback(
    standard_proof_event_t *event) {
  struct proof_task *task = standard_proof_context_get_0();
  standard_proof_context_set_0(NULL);
  if (task == NULL) {
    return_error("the C proof callback lost its task context");
    return STANDARD_PROOF_CALLBACK_CODE_EXIT;
  }

  standard_proof_waitable_join(task->subtask, 0);
  if (event->event == STANDARD_PROOF_EVENT_CANCEL) {
    standard_proof_subtask_cancel(task->subtask);
    standard_proof_subtask_drop(task->subtask);
    standard_proof_waitable_set_drop(task->wait_set);
    free(task);
    standard_proof_task_cancel();
    return STANDARD_PROOF_CALLBACK_CODE_EXIT;
  }

  if (event->event != STANDARD_PROOF_EVENT_SUBTASK ||
      event->waitable != task->subtask ||
      STANDARD_PROOF_SUBTASK_STATE(event->code) !=
          STANDARD_PROOF_SUBTASK_RETURNED) {
    standard_proof_subtask_drop(task->subtask);
    standard_proof_waitable_set_drop(task->wait_set);
    free(task);
    return_error("the C proof received an unexpected async event");
    return STANDARD_PROOF_CALLBACK_CODE_EXIT;
  }

  standard_proof_subtask_drop(task->subtask);
  standard_proof_waitable_set_drop(task->wait_set);
  return finish_fetch(task);
}

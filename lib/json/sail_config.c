/****************************************************************************/
/*     Sail                                                                 */
/*                                                                          */
/*  Sail and the Sail architecture models here, comprising all files and    */
/*  directories except the ASL-derived Sail code in the aarch64 directory,  */
/*  are subject to the BSD two-clause licence below.                        */
/*                                                                          */
/*  The ASL derived parts of the ARMv8.3 specification in                   */
/*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               */
/*                                                                          */
/*  Copyright (c) 2024                                                      */
/*    Alasdair Armstrong                                                    */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  This work was partially supported by EPSRC grant EP/K008528/1 <a        */
/*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          */
/*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   */
/*  KTF funding, and donations from Arm.  This project has received         */
/*  funding from the European Research Council (ERC) under the European     */
/*  Union’s Horizon 2020 research and innovation programme (grant           */
/*  agreement No 789108, ELVER).                                            */
/*                                                                          */
/*  This software was developed by SRI International and the University of  */
/*  Cambridge Computer Laboratory (Department of Computer Science and       */
/*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        */
/*  and FA8750-10-C-0237 ("CTSRD").                                         */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/****************************************************************************/

#include "sail_config.h"
#include "cJSON.h"

#ifdef __cplusplus
extern "C" {
#endif

struct sail_json
{
  cJSON json;
};

typedef struct sail_json* sail_config_json;

static cJSON *sail_config;

void sail_config_set_file(const char *path)
{
  cJSON_Hooks hooks;
  hooks.malloc_fn = &sail_malloc;
  hooks.free_fn = &sail_free;
  cJSON_InitHooks(&hooks);

  FILE *f = fopen(path, "rb");
  fseek(f, 0, SEEK_END);
  long fsize = ftell(f);
  fseek(f, 0, SEEK_SET);

  char *buffer = (char *)sail_malloc(fsize + 1);
  fread(buffer, fsize, 1, f);
  buffer[fsize] = 0;
  fclose(f);

  sail_config = cJSON_Parse(buffer);

  if (!sail_config) {
    sail_assert(false, "Failed to parse configuration");
  }

  sail_free(buffer);
}

void sail_config_cleanup(void)
{
  sail_free(sail_config);
}

void sail_config_get_string(sail_string *str, size_t n, const char *key[])
{
  cJSON *json = (cJSON *)sail_config;

  sail_free(*str);

  for (int i = 0; i < n; i++) {
    if (cJSON_IsObject(json)) {
      json = cJSON_GetObjectItemCaseSensitive(json, key[i]);
    } else {
      sail_assert(false, "Failed to access config item");
    }
  }

  if (cJSON_IsString(json)) {
    *str = cJSON_GetStringValue(json);
  } else {
    sail_assert(false, "Expected string value in config");
  }
}

sail_config_json sail_config_get(size_t n, const char *key[])
{
  sail_config_json result;
  cJSON *json = (cJSON *)sail_config;

  for (int i = 0; i < n; i++) {
    if (cJSON_IsObject(json)) {
      json = cJSON_GetObjectItemCaseSensitive(json, key[i]);
    } else {
      sail_assert(false, "Failed to access config item");
    }
  }

  return (sail_config_json)json;
}

bool sail_config_is_object(const sail_config_json config)
{
  return cJSON_IsObject((cJSON *)config);
}

bool sail_config_object_has_key(const sail_config_json config, const sail_string key)
{
  return cJSON_HasObjectItem((cJSON *)config, key);
}

sail_config_json sail_config_object_key(const sail_config_json config, const sail_string key)
{
  return (sail_config_json)cJSON_GetObjectItemCaseSensitive((cJSON *)config, key);
}

bool sail_config_is_string(const sail_config_json config)
{
  return cJSON_IsString((cJSON *)config);
}

bool sail_config_is_array(const sail_config_json config)
{
  return cJSON_IsArray((cJSON *)config);
}

bool sail_config_is_bool_array(const sail_config_json config)
{
  if (!sail_config_is_array(config)) {
    return false;
  }

  int len = cJSON_GetArraySize((cJSON *)config);

  cJSON *value;
  cJSON_ArrayForEach(value, ((cJSON*)config)) {
    if (!cJSON_IsBool(value)) {
      return false;
    }
  }

  return true;
}

bool sail_config_is_bool_array_with_size(const sail_config_json config, mach_int expected)
{
  if (!sail_config_is_bool_array(config)) {
    return false;
  }

  int len = cJSON_GetArraySize((cJSON *)config);

  return (mach_int)len == expected;
}

void sail_config_unwrap_string(sail_string *str, const sail_config_json config)
{
  *str = cJSON_GetStringValue((cJSON *)config);
}

void sail_config_unwrap_int(sail_int *n, const sail_config_json config)
{
  char *str = cJSON_GetStringValue((cJSON *)config);
  mpz_set_str(*n, str, 10);
}

void sail_config_unwrap_bits(lbits *bv, const sail_config_json config)
{
  cJSON *json = (cJSON *)config;

  mp_bitcnt_t len = (mp_bitcnt_t)cJSON_GetArraySize(json);
  bv->len = len;
  mpz_set_ui(*bv->bits, 0);

  mp_bitcnt_t i = 0;
  cJSON *bit;
  cJSON_ArrayForEach(bit, json) {
    if (cJSON_IsTrue(bit)) {
      mpz_setbit(*bv->bits, len - i - 1);
    }
    i++;
  }
}

#ifdef __cplusplus
}
#endif

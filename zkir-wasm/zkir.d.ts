
export type ProvingProvider = {
  check(
    serializedPreimage: Uint8Array,
    keyLocation: string,
  ): Promise<(bigint | undefined)[]>;
  prove(
    serializedPreimage: Uint8Array,
    keyLocation: string,
    overwriteBindingInput?: bigint,
  ): Promise<Uint8Array>;
} & KeyMaterialProvider;

export type ProvingKeyMaterial = {
  proverKey: Uint8Array,
  verifierKey: Uint8Array,
  ir: Uint8Array,
};

export type KeyMaterialProvider = {
    lookupKey(keyLocation: string): Promise<ProvingKeyMaterial | undefined>;
    getParams(k: number): Promise<Uint8Array>;
}

export function prove(
    serializedPreimage: Uint8Array,
    provider: KeyMaterialProvider,
    overwriteBindingInput?: bigint,
): Promise<Uint8Array>;

export function check(
    serializedPreimage: Uint8Array,
    provider: KeyMaterialProvider,
): Promise<(bigint | undefined)[]>;

export function provingProvider(kmProvider: KeyMaterialProvider): ProvingProvider;

export function jsonIrToBinary(json: String): Uint8Array;

/**
 * Checks an inner proof against a key and instance, throwing if it is
 * malformed, keyed wrongly, or paired with the wrong instance.
 *
 * Stops short of the pairing that decides whether a well-formed proof is true,
 * so a false proof passes here and fails later at the ledger.
 */
export function checkInnerProof(
    vkBlob: Uint8Array,
    instance: bigint[],
    proof: Uint8Array,
): void;

export class Zkir {
  static fromJson(json: string): Zkir;
  static deserialize(bytes: Uint8Array): Zkir;

  private constructor();
  getK(): number;
  serialize(): Uint8Array;
}
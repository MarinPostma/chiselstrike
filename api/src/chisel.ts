// SPDX-FileCopyrightText: © 2021 ChiselStrike <info@chiselstrike.com>

/// <reference types="./lib.deno_core.d.ts" />
/// <reference lib="dom" />

enum OpType {
    BaseEntity = "BaseEntity",
    Take = "Take",
    ColumnsSelect = "ColumnsSelect",
    RestrictionFilter = "RestrictionFilter",
    PredicateFilter = "PredicateFilter",
    Sort = "Sort",
}

/**
 * Base class for various Operators applicable on `ChiselCursor`. Each operator
 * should extend this class and pass on its `type` identifier from the `OpType`
 * enum.
 */
abstract class Operator {
    constructor(
        public readonly type: OpType,
        public readonly inner: Operator | undefined,
    ) {}

    /** Applies specified Operator `op` on each element of passed iterable
     * `iter` creating a new iterable.
     */
    public abstract apply(
        iter: AsyncIterable<Record<string, unknown>>,
    ): AsyncIterable<Record<string, unknown>>;
}

/**
 * Specifies Entity whose elements are to be fetched.
 */
class BaseEntity extends Operator {
    constructor(
        public name: string,
    ) {
        super(OpType.BaseEntity, undefined);
    }

    apply(
        _iter: AsyncIterable<Record<string, unknown>>,
    ): AsyncIterable<Record<string, unknown>> {
        throw new Error("can't apply BaseEntity operator on an iterable");
    }
}

/**
 * Take operator takes first `count` elements from a collection.
 * The rest is ignored.
 */
class Take extends Operator {
    constructor(
        public readonly count: number,
        inner: Operator,
    ) {
        super(OpType.Take, inner);
    }

    apply(
        iter: AsyncIterable<Record<string, unknown>>,
    ): AsyncIterable<Record<string, unknown>> {
        const count = this.count;
        return {
            [Symbol.asyncIterator]: async function* () {
                if (count == 0) {
                    return;
                }
                let i = 0;
                for await (const e of iter) {
                    yield e;
                    if (++i >= count) {
                        break;
                    }
                }
            },
        };
    }
}

/**
 * Forces fetch of just the `columns` (fields) of a given entity.
 */
class ColumnsSelect extends Operator {
    constructor(
        public columns: string[],
        inner: Operator,
    ) {
        super(OpType.ColumnsSelect, inner);
    }

    apply(
        iter: AsyncIterable<Record<string, unknown>>,
    ): AsyncIterable<Record<string, unknown>> {
        const columns = this.columns;
        return {
            [Symbol.asyncIterator]: async function* () {
                for await (const arg of iter) {
                    const newObj: Record<string, unknown> = {};
                    for (const key of columns) {
                        if (arg[key] !== undefined) {
                            newObj[key] = arg[key];
                        }
                    }
                    yield newObj;
                }
            },
        };
    }
}

/**
 * PredicateFilter operator applies `predicate` on each element and keeps
 * only those for which the `predicate` returns true.
 */
class PredicateFilter extends Operator {
    constructor(
        public predicate: (arg: unknown) => boolean,
        inner: Operator,
    ) {
        super(OpType.PredicateFilter, inner);
    }

    apply(
        iter: AsyncIterable<Record<string, unknown>>,
    ): AsyncIterable<Record<string, unknown>> {
        const predicate = this.predicate;
        return {
            [Symbol.asyncIterator]: async function* () {
                for await (const arg of iter) {
                    if (predicate(arg)) {
                        yield arg;
                    }
                }
            },
        };
    }
}

/**
 * RestrictionFilter operator applies `restrictions` on each element
 * and keeps only those where field value of a field, specified
 * by restriction key, equals to restriction value.
 */
class RestrictionFilter extends Operator {
    constructor(
        public restrictions: Record<string, unknown>,
        inner: Operator,
    ) {
        super(OpType.RestrictionFilter, inner);
    }

    apply(
        iter: AsyncIterable<Record<string, unknown>>,
    ): AsyncIterable<Record<string, unknown>> {
        const restrictions = Object.entries(this.restrictions);
        return {
            [Symbol.asyncIterator]: async function* () {
                for await (const arg of iter) {
                    verifyMatch: {
                        for (const [key, value] of restrictions) {
                            if (arg[key] != value) {
                                break verifyMatch;
                            }
                        }
                        yield arg;
                    }
                }
            },
        };
    }
}

/**
 * Sort operator sorts elements using `comparator` which
 * for two elements of the iterable returns true if `lhs`
 * is considered less than `rhs`, false otherwise.
 */
class Sort extends Operator {
    constructor(
        public comparator: (lhs: unknown, rhs: unknown) => boolean,
        inner: Operator,
    ) {
        super(OpType.Sort, inner);
    }

    apply(
        iter: AsyncIterable<Record<string, unknown>>,
    ): AsyncIterable<Record<string, unknown>> {
        const cmp = this.comparator;
        return {
            [Symbol.asyncIterator]: async function* () {
                const elements = [];
                for await (const e of iter) {
                    elements.push(e);
                }
                elements.sort(
                    (lhs: unknown, rhs: unknown) => {
                        return cmp(lhs, rhs) ? -1 : 1;
                    },
                );
                for (const e of elements) {
                    yield e;
                }
            },
        };
    }
}

/** ChiselCursor is a lazy iterator that will be used by ChiselStrike to construct an optimized query. */
export class ChiselCursor<T> {
    constructor(
        private baseConstructor: { new (): T },
        private inner: Operator,
    ) {}
    /** Force ChiselStrike to fetch just the `...columns` that are part of the colums list. */
    select(...columns: (keyof T)[]): ChiselCursor<Pick<T, (keyof T)>> {
        return new ChiselCursor(
            this.baseConstructor,
            new ColumnsSelect(columns as string[], this.inner),
        );
    }

    /** Restricts this cursor to contain only at most `count` elements */
    take(count: number): ChiselCursor<T> {
        return new ChiselCursor(
            this.baseConstructor,
            new Take(count, this.inner),
        );
    }

    /**
     * Restricts this cursor to contain only elements that match the given @predicate.
     */
    filter(
        predicate: (arg: T) => boolean,
    ): ChiselCursor<T>;
    /**
     * Restricts this cursor to contain just the objects that match the `Partial`
     * object `restrictions`.
     */
    filter(restrictions: Partial<T>): ChiselCursor<T>;

    // Common implementation for filter overloads.
    filter(arg1: ((arg: T) => boolean) | Partial<T>): ChiselCursor<T> {
        if (typeof arg1 == "function") {
            return new ChiselCursor(
                this.baseConstructor,
                new PredicateFilter(
                    arg1 as ((arg: unknown) => boolean),
                    this.inner,
                ),
            );
        } else {
            return new ChiselCursor(
                this.baseConstructor,
                new RestrictionFilter(arg1, this.inner),
            );
        }
    }

    /**
     * Sorts cursor elements.
     *
     * @param comparator determines the sorting order. For two elements of the
     * iterable returns true if `lhs` is considered less than `rhs`,
     * false otherwise.
     *
     * Note: the sort is not guaranteed to be stable.
     */
    sort(
        comparator: (lhs: T, rhs: T) => boolean,
    ): ChiselCursor<T> {
        return new ChiselCursor(
            this.baseConstructor,
            new Sort(
                comparator as ((lhs: unknown, rhs: unknown) => boolean),
                this.inner,
            ),
        );
    }

    /**
     * Sorts cursor elements.
     *
     * @param key specifies which attribute of `T` is to be used as a sort key.
     * @param ascending if true, the sort will be ascending. Descending otherwise.
     *
     * Note: the sort is not guaranteed to be stable.
     */
    sortBy(key: keyof T, ascending = true): ChiselCursor<T> {
        const cmp = (lhs: T, rhs: T) => {
            return ascending === (lhs[key] < rhs[key]);
        };
        return new ChiselCursor(
            this.baseConstructor,
            new Sort(
                cmp as ((lhs: unknown, rhs: unknown) => boolean),
                this.inner,
            ),
        );
    }

    /** Executes the function `func` for each element of this cursor. */
    async forEach(func: (arg: T) => void): Promise<void> {
        for await (const t of this) {
            func(t);
        }
    }

    /** Converts this cursor to an Array.
     *
     * Use this with caution as the result set can be very big.
     * It is recommended that you take() first to cap the maximum number of elements. */
    async toArray(): Promise<Partial<T>[]> {
        const arr = [];
        for await (const t of this) {
            arr.push(t);
        }
        return arr;
    }

    /** ChiselCursor implements asyncIterator, meaning you can use it in any asynchronous context. */
    async *[Symbol.asyncIterator]() {
        let iter = this.makeTransformedQueryIter(this.inner);
        if (iter === undefined) {
            iter = this.makeQueryIter(this.inner);
        }
        for await (const it of iter) {
            yield it as T;
        }
    }

    /** Performs recursive descent via Operator.inner examining the whole operator
     * chain. If PredicateFilter or Sort is encountered, a backend query is generated
     * and all consecutive operations are applied on the resulting async iterable
     * in TypeScript. In such a case, the function returns the resulting AsyncIterable.
     * If no PredicateFilter or Sort is found, undefined is returned.
     */
    private makeTransformedQueryIter(
        op: Operator,
    ): AsyncIterable<Record<string, unknown>> | undefined {
        if (op.type == OpType.BaseEntity) {
            return undefined;
        } else if (op.inner === undefined) {
            throw new Error(
                "internal error: expected inner operator, got undefined",
            );
        }
        let iter = this.makeTransformedQueryIter(op.inner);
        if (iter !== undefined) {
            return op.apply(iter);
        } else if (
            op.type == OpType.PredicateFilter || op.type == OpType.Sort
        ) {
            iter = this.makeQueryIter(op.inner);
            return op.apply(iter);
        } else {
            return undefined;
        }
    }

    private makeQueryIter(
        op: Operator,
    ): AsyncIterable<Record<string, unknown>> {
        const ctor = this.containsSelect(op) ? undefined : this.baseConstructor;
        return {
            [Symbol.asyncIterator]: async function* () {
                const rid = Deno.core.opSync(
                    "chisel_relational_query_create",
                    op,
                );
                try {
                    while (true) {
                        const properties = await Deno.core.opAsync(
                            "chisel_relational_query_next",
                            rid,
                        );

                        if (properties == undefined) {
                            break;
                        }
                        if (ctor !== undefined) {
                            const result = new ctor();
                            Object.assign(result, properties);
                            yield result;
                        } else {
                            yield properties;
                        }
                    }
                } finally {
                    Deno.core.opSync("op_close", rid);
                }
            },
        };
    }

    /** Recursively examines operator chain searching for ColumnsSelect operator.
     * Returns true if found, false otherwise.
     */
    private containsSelect(op: Operator): boolean {
        if (op.type == OpType.ColumnsSelect) {
            return true;
        } else if (op.inner === undefined) {
            return false;
        } else {
            return this.containsSelect(op.inner);
        }
    }
}

export function chiselIterator<T>(type: { new (): T }) {
    const b = new BaseEntity(type.name);
    return new ChiselCursor<T>(type, b);
}

/** ChiselEntity is a class that ChiselStrike user-defined entities are expected to extend.
 *
 * It provides properties that are inherent to a ChiselStrike entity, like an id, and static
 * methods that can be used to obtain a `ChiselCursor`.
 */
export class ChiselEntity {
    /** UUID identifying this object. */
    id?: string;

    /**
     * Builds a new entity.
     *
     * @param properties The properties of the created entity. If more than one property
     * is passed, the expected order of assignment is the same as Object.assign.
     *
     * @example
     * ```typescript
     * export class User extends ChiselEntity {
     *   username: string,
     *   email: string,
     * }
     * // Create an entity from object literal:
     * const user = User.build({ username: "alice", email: "alice@example.com" });
     * // Create an entity from JSON:
     * const userJson = JSON.parse('{"username": "alice", "email": "alice@example.com"}');
     * const anotherUser = User.build(userJson);
     *
     * // Create an entity from different JSON objects:
     * const otherUserJson = JSON.parse('{"username": "alice"}, {"email": "alice@example.com"}');
     * const yetAnotherUser = User.build(userJson);
     *
     * // now optionally save them to the backend
     * await user.save();
     * await anotherUser.save();
     * await yetAnotherUser.save();
     * ```
     * @returns The persisted entity with given properties and the `id` property set.
     */
    static build<T extends ChiselEntity>(
        this: { new (): T },
        ...properties: Record<string, unknown>[]
    ): T {
        const result = new this();
        Object.assign(result, ...properties);
        return result;
    }

    /** saves the current object into the backend */
    async save() {
        const jsonIds = await Deno.core.opAsync("chisel_store", {
            name: this.constructor.name,
            value: this,
        });
        type IdsJson = Map<string, IdsJson>;
        function backfillIds(this_: ChiselEntity, jsonIds: IdsJson) {
            for (const [fieldName, value] of Object.entries(jsonIds)) {
                if (fieldName == "id") {
                    this_.id = value as string;
                } else {
                    const child = (this_ as unknown as Record<string, unknown>)[
                        fieldName
                    ];
                    backfillIds(child as ChiselEntity, value);
                }
            }
        }
        backfillIds(this, jsonIds);
    }

    /** Returns a `ChiselCursor` containing all elements of type T known to ChiselStrike.
     *
     * Note that `ChiselCursor` is a lazy iterator, so this doesn't mean a query will be generating fetching all elements at this point. */
    static cursor<T>(
        this: { new (): T },
    ): ChiselCursor<T> {
        return chiselIterator<T>(this);
    }

    /** Restricts this iterator to contain just the objects that match the `Partial` object `restrictions`. */
    static async findMany<T>(
        this: { new (): T },
        restrictions: Partial<T>,
        take?: number,
    ): Promise<Partial<T>[]> {
        let it = chiselIterator<T>(this);
        if (take) {
            it = it.take(take);
        }
        return await it.filter(restrictions).toArray();
    }

    /** Returns a single object that matches the `Partial` object `restrictions` passed as its parameter.
     *
     * If more than one match is found, any is returned. */
    static async findOne<T extends ChiselEntity>(
        this: { new (): T },
        restrictions: Partial<T>,
    ): Promise<T | null> {
        const it = chiselIterator<T>(this).filter(restrictions).take(1);
        for await (const value of it) {
            return value;
        }
        return null;
    }

    /**
     * Deletes all entities that match the `restrictions` object.
     *
     * @example
     * ```typescript
     * export class User extends ChiselEntity {
     *   username: string,
     *   email: string,
     * }
     * const user = User.build({ username: "alice", email: "alice@example.com" });
     * await user.save();
     *
     * await User.delete({ email: "alice@example.com"})
     * ```
     */
    static async delete<T extends ChiselEntity>(
        this: { new (): T },
        restrictions: Partial<T>,
    ): Promise<void> {
        await Deno.core.opAsync("chisel_entity_delete", {
            type_name: this.name,
            restrictions: restrictions,
        });
    }

    /**
     * Convenience method for crud() below.
     */
    static crud(p: string) {
        return crud(this, p);
    }
}

export class OAuthUser extends ChiselEntity {
    username: string | undefined = undefined;
}

export function buildReadableStreamForBody(rid: number) {
    return new ReadableStream<string>({
        async pull(controller: ReadableStreamDefaultController) {
            const chunk = await Deno.core.opAsync("chisel_read_body", rid);
            if (chunk) {
                controller.enqueue(chunk);
            } else {
                controller.close();
                Deno.core.opSync("op_close", rid);
            }
        },
        cancel() {
            Deno.core.opSync("op_close", rid);
        },
    });
}

/**
 * Gets a secret from the environment
 *
 * To allow a secret to be used, the server has to be run with * --allow-env <YOUR_SECRET>
 *
 * In development mode, all of your environment variables are accessible
 */
type JSONValue =
    | string
    | number
    | boolean
    | null
    | { [x: string]: JSONValue }
    | Array<JSONValue>;

export function getSecret(key: string): JSONValue | undefined {
    const secret = Deno.core.opSync("chisel_get_secret", key);
    if (secret === undefined || secret === null) {
        return undefined;
    }
    return secret;
}

export function responseFromJson(body: unknown, status = 200) {
    // https://fetch.spec.whatwg.org/#null-body-status
    const isNullBody = (status: number): boolean => {
        return status == 101 || status == 204 || status == 205 || status == 304;
    };

    const json = isNullBody(status) ? null : JSON.stringify(body);
    return new Response(json, {
        status: status,
        headers: [
            ["content-type", "application/json"],
        ],
    });
}

export function labels(..._val: string[]) {
    return <T>(_target: T, _propertyName: string) => {
        // chisel-decorator, no content
    };
}

export function unique(): void {
    // chisel-decorator, no content
}

/** Returns the currently logged-in user or null if no one is logged in. */
export async function loggedInUser(): Promise<OAuthUser | null> {
    const id = await Deno.core.opAsync("chisel_user", {});
    return id == null ? null : await OAuthUser.findOne({ id });
}

// TODO: BEGIN: this should be in another file: crud.ts

// TODO: BEGIN: when module import is fixed:
//     import { parse as regExParamParse } from "regexparam";
// or:
//     import { parse as regExParamParse } from "regexparam";
// In the meantime, the regExParamParse function is copied from
// https://deno.land/x/regexparam@v2.0.0/src/index.js under MIT License included
// below. ChiselStrike added the TS signature and minor cleanups.
//
// Copyright (c) Luke Edwards <luke.edwards05@gmail.com> (lukeed.com)
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.
export function regExParamParse(str: string, loose: boolean) {
    let tmp, pattern = "";
    const keys = [], arr = str.split("/");
    arr[0] || arr.shift();

    while ((tmp = arr.shift())) {
        const c = tmp[0];
        if (c === "*") {
            keys.push("wild");
            pattern += "/(.*)";
        } else if (c === ":") {
            const o = tmp.indexOf("?", 1);
            const ext = tmp.indexOf(".", 1);
            keys.push(tmp.substring(1, ~o ? o : ~ext ? ext : tmp.length));
            pattern += !!~o && !~ext ? "(?:/([^/]+?))?" : "/([^/]+?)";
            if (~ext) pattern += (~o ? "?" : "") + "\\" + tmp.substring(ext);
        } else {
            pattern += "/" + tmp;
        }
    }

    return {
        keys: keys,
        pattern: new RegExp("^" + pattern + (loose ? "(?=$|/)" : "/?$"), "i"),
    };
}
// TODO: END: when module import is fixed

type ChiselEntityClass<T extends ChiselEntity> = {
    new (): T;
    findOne: (_: { id: string }) => Promise<T | null>;
    findMany: (_: Partial<T>) => Promise<Partial<T>[]>;
    build: (...properties: Record<string, unknown>[]) => T;
    delete: (restrictions: Partial<T>) => Promise<void>;
};

type GenericChiselEntityClass = ChiselEntityClass<ChiselEntity>;

/**
 * Get the filters to be used with a ChiselEntity from a URL.
 *
 * This will get the URL search parameter "f" and assume it's a JSON object.
 * @param _entity the entity class that will be filtered
 * @param url the url that provides the search parameters
 * @returns the partial filters, note that it may return an empty object, meaning all objects will be returned/deleted.
 */
export function getEntityFiltersFromURL<
    T extends ChiselEntity,
    E extends ChiselEntityClass<T>,
>(_entity: E, url: URL): Partial<T> | undefined {
    // TODO: it's more common to have filters as regular query parameters, URI-encoded,
    // then entity may be used to get such field names
    // TODO: validate if unknown filters where given?
    const f = url.searchParams.get("f");
    if (!f) {
        return undefined;
    }
    const o = JSON.parse(decodeURI(f));
    if (o && typeof o === "object") {
        return o;
    }
    throw new Error(`provided search parameter 'f=${f}' is not a JSON object.`);
}

/**
 * Creates a path parser from a template using regexparam.
 *
 * @param pathTemplate the path template such as `/static`, `/param/:id/:otherParam`...
 * @param loose if true, it can match longer paths. False by default
 * @returns function that can parse paths given as string.
 * @see https://deno.land/x/regexparam@v2.0.0
 */
export function createPathParser<T extends Record<string, unknown>>(
    pathTemplate: string,
    loose = false,
): ((path: string) => T) {
    const { pattern, keys: keysOrFalse } = regExParamParse(pathTemplate, loose);
    if (typeof keysOrFalse === "boolean") {
        throw new Error(
            `invalid pathTemplate=${pathTemplate}, expected string`,
        );
    }
    const keys = keysOrFalse;
    return function pathParser(path: string): T {
        const matches = pattern.exec(path);
        return keys.reduce(
            (acc: Record<string, unknown>, key: string, index: number) => {
                acc[key] = matches?.[index + 1];
                return acc;
            },
            {},
        ) as T;
    };
}

/**
 * Creates a path parser from a template using regexparam.
 *
 * @param pathTemplate the path template such as `/static`, `/param/:id/:otherParam`...
 * @param loose if true, it can match longer paths. False by default
 * @returns function that can parse paths given in URL.pathname.
 * @see https://deno.land/x/regexparam@v2.0.0
 */
export function createURLPathParser<T extends Record<string, unknown>>(
    pathTemplate: string,
    loose = false,
): ((url: URL) => T) {
    const pathParser = createPathParser<T>(pathTemplate, loose);
    return (url: URL): T => pathParser(url.pathname);
}

/** Creates a Response object from response body and status. */
export type CRUDCreateResponse = (
    body: unknown,
    status: number,
) => (Promise<Response> | Response);

export type CRUDBaseParams = {
    /** identifier of the object being manipulated, if any */
    id?: string;
    /** ChiselStrike's version/branch the server is running,
     * such as 'dev' for endpoint '/dev/example'
     * when using 'chisel apply --version dev'
     */
    chiselVersion: string;
};

export type CRUDMethodSignature<
    T extends ChiselEntity,
    E extends ChiselEntityClass<T>,
    P extends CRUDBaseParams = CRUDBaseParams,
> = (
    entity: E,
    req: Request,
    params: P,
    url: URL,
    createResponse: CRUDCreateResponse,
) => Promise<Response>;

/**
 * A dictionary mapping HTTP verbs into corresponding REST methods that process a Request and return a Response.
 */
export type CRUDMethods<
    T extends ChiselEntity,
    E extends ChiselEntityClass<T>,
    P extends CRUDBaseParams = CRUDBaseParams,
> = {
    GET: CRUDMethodSignature<T, E, P>;
    POST: CRUDMethodSignature<T, E, P>;
    PUT: CRUDMethodSignature<T, E, P>;
    DELETE: CRUDMethodSignature<T, E, P>;
};

export type CRUDCreateResponses<
    T extends ChiselEntity,
    E extends ChiselEntityClass<T>,
    P extends CRUDBaseParams = CRUDBaseParams,
> = {
    [K in keyof CRUDMethods<T, E, P>]: CRUDCreateResponse;
};

const defaultCrudMethods: CRUDMethods<ChiselEntity, GenericChiselEntityClass> =
    {
        // Returns a specific entity matching params.id (if present) or all entities matching the filter in the `f` URL parameter.
        GET: async (
            entity: GenericChiselEntityClass,
            _req: Request,
            params: CRUDBaseParams,
            url: URL,
            createResponse: CRUDCreateResponse,
        ) => {
            const { id } = params;
            if (!id) {
                return createResponse(
                    await entity.findMany(
                        getEntityFiltersFromURL(entity, url) || {},
                    ),
                    200,
                );
            }
            const u = await entity.findOne({ id });
            return createResponse(u ?? "Not found", u ? 200 : 404);
        },
        // Creates and returns a new entity from the `req` payload. Ignores the payload's id property and assigns a fresh one.
        POST: async (
            entity: GenericChiselEntityClass,
            req: Request,
            _params: CRUDBaseParams,
            _url: URL,
            createResponse: CRUDCreateResponse,
        ) => {
            const u = entity.build(await req.json());
            u.id = undefined;
            await u.save();
            return createResponse(u, 200);
        },
        // Updates and returns the entity matching params.id (which must be set) from the `req` payload.
        PUT: async (
            entity: GenericChiselEntityClass,
            req: Request,
            params: CRUDBaseParams,
            _url: URL,
            createResponse: CRUDCreateResponse,
        ) => {
            const { id } = params;
            if (!id) {
                return createResponse(
                    "PUT requires item ID in the URL",
                    400,
                );
            }
            const u = entity.build(await req.json());
            u.id = id;
            await u.save();
            return createResponse(u, 200);
        },
        // Deletes the entity matching params.id (if present) or all entities matching the filter in the `f` URL parameter.
        // IF `f` IS ABSENT, DELETES ALL ENTITIES!
        DELETE: async (
            entity: GenericChiselEntityClass,
            _req: Request,
            params: CRUDBaseParams,
            url: URL,
            createResponse: CRUDCreateResponse,
        ) => {
            const { id } = params;
            const restrictions = !id
                ? getEntityFiltersFromURL(entity, url)
                : { id };
            await entity.delete(restrictions || {}); // TODO: should a missing filter really remove all entities?
            return createResponse("Deletion successful!", 200);
        },
    } as const;

/**
 * These methods can be used as `customMethods` in `ChiselStrike.crud()`.
 *
 * @example
 * Put this in the file 'endpoints/comments.ts':
 * ```typescript
 * import { Comment } from "../models/comment";
 * export default crud(
 *   Comment,
 *   '/comments/:id',
 *   {
 *     PUT: standardCRUDMethods.notFound, // do not update, instead returns 404
 *     DELETE: standardCRUDMethods.methodNotAllowed, // do not delete, instead returns 405
 *   },
 * );
 * ```
 */
export const standardCRUDMethods = {
    forbidden: (
        _entity: GenericChiselEntityClass,
        _req: Request,
        _params: CRUDBaseParams,
        _url: URL,
        createResponse: CRUDCreateResponse,
    ) => Promise.resolve(createResponse("Forbidden", 403)),
    notFound: (
        _entity: GenericChiselEntityClass,
        _req: Request,
        _params: CRUDBaseParams,
        _url: URL,
        createResponse: CRUDCreateResponse,
    ) => Promise.resolve(createResponse("Not Found", 404)),
    methodNotAllowed: (
        _entity: GenericChiselEntityClass,
        _req: Request,
        _params: CRUDBaseParams,
        _url: URL,
        createResponse: CRUDCreateResponse,
    ) => Promise.resolve(createResponse("Method Not Allowed", 405)),
} as const;

/**
 * Generates endpoint code to handle REST methods GET/PUT/POST/DELETE for this entity.
 * @example
 * Put this in the file 'endpoints/comments.ts':
 * ```typescript
 * import { Comment } from "../models/comment";
 * export default crud(Comment, "/comments/:id");
 * ```
 * This results in a /comments endpoint that correctly handles all REST methods over Comment.
 * @param entity Entity type
 * @param urlTemplate Request URL must match this template (see https://deno.land/x/regexparam for syntax).
 *   Some CRUD methods rely on parts of the URL to identify the resource to apply to. Eg, GET /comments/1234
 *   returns the comment entity with id=1234, while GET /comments returns all comments. This parameter describes
 *   how to find the relevant parts in the URL. Default CRUD methods (see `defaultCrudMethods`) look for the :id
 *   part in this template to identify specific entity instances. If there is no :id in the template, then '/:id'
 *   is automatically added to its end. Custom methods can use other named parts. NOTE: because of file-based
 *   routing, `urlTemplate` must necessarily begin with the path of the endpoint invoking this function; it's the
 *   only way for the request URL to match it. Eg, if `crud()` is invoked by the file `endpoints/a/b/foo.ts`, the
 *   `urlTemplate` must begin with 'a/b/foo'; in fact, it can be exactly 'a/b/foo', taking advantage of reasonable
 *   defaults to ensure that the created RESTful API works as you would expect.
 * @param config Configure the CRUD behavior:
 *  - `customMethods`: custom request handlers overriding the defaults.
 *     Each present property overrides that method's handler. You can use `standardCRUDMethods` members here to
 *     conveniently reject some actions. When `customMethods` is absent, we use methods from `defaultCrudMethods`.
 *     Note that these default methods look for the `id` property in their `params` argument; if set, its value is
 *     the id of the entity to process. Conveniently, the default `urlTemplate` parser sets this property from the
 *     `:id` pattern.
 *  - `createResponses`: if present, a dictionary of method-specific Response creators.
 *  - `defaultCreateResponse`: default function to create all responses if `createResponses` entry is not provided.
 *     Defaults to `responseFromJson()`.
 *  - `parsePath`: parses the URL path instead of https://deno.land/x/regexparam. The parsing result is passed to
 *     CRUD methods as the `params` argument.
 * @returns A request-handling function suitable as a default export in an endpoint.
 */
export function crud<
    T extends ChiselEntity,
    E extends ChiselEntityClass<T>,
    P extends CRUDBaseParams = CRUDBaseParams,
>(
    entity: E,
    urlTemplate: string,
    config?: {
        customMethods?: Partial<CRUDMethods<T, ChiselEntityClass<T>, P>>;
        createResponses?: Partial<
            CRUDCreateResponses<T, ChiselEntityClass<T>, P>
        >;
        defaultCreateResponse?: CRUDCreateResponse;
        parsePath?: (url: URL) => P;
    },
): (req: Request) => Promise<Response> {
    const pathTemplate = "/:chiselVersion" +
        (urlTemplate.startsWith("/") ? "" : "/") +
        (urlTemplate.includes(":id") ? urlTemplate : `${urlTemplate}/:id`);

    const defaultCreateResponse = config?.defaultCreateResponse ||
        responseFromJson;
    const parsePath = config?.parsePath ||
        createURLPathParser(pathTemplate);
    const localDefaultCrudMethods =
        defaultCrudMethods as unknown as CRUDMethods<T, E, P>;
    const methods = config?.customMethods
        ? { ...localDefaultCrudMethods, ...config?.customMethods }
        : localDefaultCrudMethods;

    return (req: Request): Promise<Response> => {
        const methodName = req.method as keyof typeof methods; // assume valid, will be handled gracefully
        const createResponse = config?.createResponses?.[methodName] ||
            defaultCreateResponse;
        const method = methods[methodName];
        if (!method) {
            return Promise.resolve(
                createResponse(`Unsupported HTTP method: ${methodName}`, 405),
            );
        }

        const url = new URL(req.url);
        const params = parsePath(url);
        return method(entity, req, params, url, createResponse);
    };
}
// TODO: END: this should be in another file: crud.ts

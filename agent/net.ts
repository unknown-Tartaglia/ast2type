/**
 * 网络代理配置 - 可复用模块
 *
 * 使用方式：
 *   import { setupProxy } from "./agent/net";
 *   setupProxy(); // 所有 fetch 请求走代理
 *
 * 环境变量：
 *   HTTP_PROXY  - 默认 http://127.0.0.1:10805
 *   NO_PROXY_TLS - 设为 1 跳过 TLS 证书校验
 */

let _setup = false;

export type AgentProvider = "deepseek" | "openai";

export interface AgentConfig {
  provider: AgentProvider;
  apiKey: string;
  baseUrl: string;
  model: string;
}

export interface AgentConfigInput {
  provider?: string;
  apiKey?: string;
  baseUrl?: string;
  model?: string;
}

export interface AgentMessage {
  role: string;
  content: string;
}

export interface ChatOptions {
  messages: AgentMessage[];
  tools?: Array<Record<string, unknown>>;
  /** OpenAI Responses API 的严格结构化文本输出；DeepSeek 路径不会使用。 */
  structuredOutput?: {
    name: string;
    schema: Record<string, unknown>;
  };
  /** 整个请求（包括读取 SSE 正文）的超时时间。 */
  timeoutMs?: number;
}

export interface AgentChatRequest {
  url: string;
  body: Record<string, unknown>;
}

const PROVIDER_DEFAULTS: Record<AgentProvider, { baseUrl: string; model: string }> = {
  deepseek: {
    baseUrl: "https://api.deepseek.com/v1",
    model: "deepseek-chat",
  },
  openai: {
    baseUrl: "https://api.openai.com/v1",
    model: "gpt-4.1-mini",
  },
};

export function getAgentApiKeyEnvName(provider: AgentProvider): string {
  return provider === "openai" ? "OPENAI_API_KEY" : "DEEPSEEK_API_KEY";
}

/** 将 CLI 与环境变量收敛为一个显式配置，避免各入口使用不同默认值。 */
export function resolveAgentConfig(
  input: AgentConfigInput = {},
  env: NodeJS.ProcessEnv = process.env,
): AgentConfig {
  const rawProvider = input.provider || env.AGENT_PROVIDER || "deepseek";
  const provider = rawProvider.trim().toLowerCase();
  if (provider !== "deepseek" && provider !== "openai") {
    throw new Error(
      `Invalid agent provider "${rawProvider}"; expected deepseek or openai`,
    );
  }

  const typedProvider = provider as AgentProvider;
  const providerPrefix = typedProvider === "openai" ? "OPENAI" : "DEEPSEEK";
  const defaults = PROVIDER_DEFAULTS[typedProvider];
  const apiKeyEnvName = getAgentApiKeyEnvName(typedProvider);
  const baseUrl =
    input.baseUrl ||
    env.AGENT_BASE_URL ||
    env[`${providerPrefix}_BASE_URL`] ||
    defaults.baseUrl;

  return {
    provider: typedProvider,
    apiKey: input.apiKey || env[apiKeyEnvName] || "",
    baseUrl: baseUrl.trim().replace(/\/+$/, ""),
    model:
      input.model ||
      env.AGENT_MODEL ||
      env[`${providerPrefix}_MODEL`] ||
      defaults.model,
  };
}

export async function setupProxy(proxyUrl?: string) {
  if (_setup) return;
  _setup = true;

  if (typeof globalThis.File === "undefined") {
    (globalThis as any).File = class File extends Blob {
      name: string;
      lastModified: number;
      constructor(bits: any[], name: string, opts?: any) {
        super(bits, opts);
        this.name = name;
        this.lastModified = opts?.lastModified ?? Date.now();
      }
    } as any;
  }

  const { ProxyAgent, setGlobalDispatcher } = await import("undici");

  const uri = proxyUrl || process.env.HTTP_PROXY || "http://127.0.0.1:10805";
  const rejectUnauthorized = process.env.NO_PROXY_TLS !== "1";

  setGlobalDispatcher(
    new ProxyAgent({ uri, requestTls: { rejectUnauthorized } })
  );
}

/** 便捷方法: 带代理的 fetch，无需 setupProxy 也可直接用 */
export async function fetchWithProxy(
  url: string,
  init?: RequestInit
): Promise<Response> {
  await setupProxy();
  return fetch(url, init);
}

const OPENAI_REASONING_EFFORTS = new Set([
  "none",
  "minimal",
  "low",
  "medium",
  "high",
  "xhigh",
  "max",
]);

/**
 * GPT-5.1+ 在省略 reasoning.effort 时可能执行较多推理；类型批处理更重视吞吐，
 * 因此默认关闭推理。其他模型保持服务端默认，避免向不支持该字段的模型发送参数。
 * 可用 OPENAI_REASONING_EFFORT=default 恢复服务端默认，或显式指定 effort。
 */
function resolveOpenAIReasoningEffort(model: string): string | undefined {
  const configured = process.env.OPENAI_REASONING_EFFORT?.trim().toLowerCase();
  if (configured === "default") return undefined;
  if (configured) {
    if (!OPENAI_REASONING_EFFORTS.has(configured)) {
      throw new Error(
        `Invalid OPENAI_REASONING_EFFORT "${configured}"; expected ` +
        "default, none, minimal, low, medium, high, xhigh, or max",
      );
    }
    return configured;
  }

  const normalizedModel = model.toLowerCase();
  // Pro 型号通常只接受 medium/high 等较高档位，不能自动发送 none。
  if (/(?:^|-)pro(?:-|$)/.test(normalizedModel)) return undefined;
  const version = normalizedModel.match(/^gpt-5\.(\d+)(?:[.-]|$)/);
  return version && Number(version[1]) >= 1 ? "none" : undefined;
}

/**
 * 默认对常规模型启用 Structured Outputs；已知不支持的型号自动回退到 prompt JSON。
 * OpenAI 兼容反代可用 OPENAI_STRUCTURED_OUTPUT=0/1 显式覆盖能力判断。
 */
export function supportsOpenAIStructuredOutput(model: string): boolean {
  const configured = process.env.OPENAI_STRUCTURED_OUTPUT?.trim().toLowerCase();
  if (["0", "false", "off", "no"].includes(configured || "")) return false;
  if (["1", "true", "on", "yes"].includes(configured || "")) return true;
  return !/^gpt-5\.4-pro(?:-|$)/i.test(model);
}

/** 构造 provider 对应的原生 HTTP 请求，供调用代码和回归测试共用。 */
export function buildChatRequest(
  config: AgentConfig,
  opts: ChatOptions,
): AgentChatRequest {
  const body: Record<string, unknown> = { model: config.model };
  let endpoint: string;

  if (config.provider === "openai") {
    endpoint = "responses";
    body.input = opts.messages;
    const reasoningEffort = resolveOpenAIReasoningEffort(config.model);
    if (reasoningEffort) {
      body.reasoning = { effort: reasoningEffort };
    }
    if (opts.structuredOutput && supportsOpenAIStructuredOutput(config.model)) {
      body.text = {
        format: {
          type: "json_schema",
          name: opts.structuredOutput.name,
          strict: true,
          schema: opts.structuredOutput.schema,
        },
      };
    }
  } else {
    endpoint = "chat/completions";
    body.messages = opts.messages;
    body.temperature = 0;
  }
  if (opts.tools?.length) body.tools = opts.tools;

  return {
    url: `${config.baseUrl.replace(/\/+$/, "")}/${endpoint}`,
    body,
  };
}

/** 把不同 provider 的响应统一成 infer.ts 所需的 content 字段。 */
export function parseChatResponse(
  provider: AgentProvider,
  data: any,
): { content: string } {
  if (provider === "deepseek") {
    const content = data?.choices?.[0]?.message?.content;
    if (typeof content !== "string") {
      throw new Error("DeepSeek response is missing choices[0].message.content");
    }
    return { content };
  }

  // Responses API 的文本位于 output message 的 output_text content 中。
  const texts: string[] = [];
  if (Array.isArray(data?.output)) {
    for (const item of data.output) {
      if (!Array.isArray(item?.content)) continue;
      for (const part of item.content) {
        if (part?.type === "output_text" && typeof part.text === "string") {
          texts.push(part.text);
        }
      }
    }
  }

  // 某些兼容实现会直接返回聚合后的 output_text。
  if (texts.length === 0 && typeof data?.output_text === "string") {
    texts.push(data.output_text);
  }
  if (texts.length === 0) {
    throw new Error("OpenAI response is missing output_text content");
  }
  return { content: texts.join("") };
}

function streamErrorMessage(data: any): string {
  const error = data?.error || data?.response?.error;
  return error?.message || data?.message || "unknown streaming error";
}

/**
 * 解析 Responses API 的 SSE 返回。
 *
 * 部分反代即使未请求 stream 也始终返回 text/event-stream，而且 completed
 * 事件可能不携带完整 output。因此优先使用 completed 中的完整文本，缺失时
 * 再使用 output_text.done 或按顺序拼接 output_text.delta。
 */
export function parseOpenAIEventStream(payload: string): { content: string } {
  const normalized = payload.replace(/^\uFEFF/, "").replace(/\r\n?/g, "\n");
  const deltas: string[] = [];
  const doneTexts: string[] = [];
  let completedText: string | undefined;
  let terminalSeen = false;
  let parsedEvents = 0;

  for (const block of normalized.split(/\n\n+/)) {
    if (!block.trim()) continue;

    let eventName = "";
    const dataLines: string[] = [];
    for (const line of block.split("\n")) {
      if (!line || line.startsWith(":")) continue;
      const colon = line.indexOf(":");
      const field = colon === -1 ? line : line.slice(0, colon);
      let value = colon === -1 ? "" : line.slice(colon + 1);
      if (value.startsWith(" ")) value = value.slice(1);
      if (field === "event") eventName = value;
      if (field === "data") dataLines.push(value);
    }
    if (dataLines.length === 0) continue;

    const rawData = dataLines.join("\n");
    if (rawData === "[DONE]") {
      terminalSeen = true;
      continue;
    }

    let data: any;
    try {
      data = JSON.parse(rawData);
    } catch (error) {
      const detail = error instanceof Error ? error.message : String(error);
      throw new Error(`OpenAI SSE event ${eventName || "unknown"} contains invalid JSON: ${detail}`);
    }
    parsedEvents++;

    const eventType = data?.type || eventName;
    if (eventType === "error" || eventType === "response.failed") {
      throw new Error(`OpenAI streaming response failed: ${streamErrorMessage(data)}`);
    }
    if (eventType === "response.incomplete") {
      throw new Error(`OpenAI streaming response incomplete: ${streamErrorMessage(data)}`);
    }
    if (eventType === "response.output_text.delta" && typeof data.delta === "string") {
      deltas.push(data.delta);
      continue;
    }
    if (eventType === "response.output_text.done" && typeof data.text === "string") {
      doneTexts.push(data.text);
      continue;
    }
    if (eventType === "response.completed") {
      terminalSeen = true;
      const response = data?.response || data;
      if (response?.error) {
        throw new Error(`OpenAI streaming response failed: ${streamErrorMessage(response)}`);
      }
      try {
        completedText = parseChatResponse("openai", response).content;
      } catch (error) {
        // 某些反代的 completed.output 为空；此时使用之前收到的文本事件。
        if (!(error instanceof Error) || !error.message.includes("missing output_text")) {
          throw error;
        }
      }
    }
  }

  if (parsedEvents === 0) {
    throw new Error("OpenAI streaming response contains no events");
  }
  if (!terminalSeen) {
    throw new Error("OpenAI streaming response ended before response.completed");
  }

  const content = completedText ?? (doneTexts.length > 0 ? doneTexts.join("") : deltas.join(""));
  if (!content) {
    throw new Error("OpenAI streaming response is missing output_text content");
  }
  return { content };
}

/** LLM API 直接调用封装；传入 fetchImpl 时不会初始化全局代理，便于离线测试。 */
export async function chat(
  config: AgentConfig,
  opts: ChatOptions,
  fetchImpl?: typeof fetch,
): Promise<{ content: string }> {
  if (!config.apiKey) {
    throw new Error(`Missing API key for ${config.provider}`);
  }
  if (!fetchImpl) await setupProxy();

  const request = buildChatRequest(config, opts);
  const executeFetch = fetchImpl || fetch;
  const envTimeout = Number(process.env.AGENT_REQUEST_TIMEOUT_MS);
  const timeoutMs = opts.timeoutMs ?? (
    Number.isFinite(envTimeout) && envTimeout > 0 ? envTimeout : 10 * 60 * 1000
  );
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), timeoutMs);

  try {
    const res = await executeFetch(request.url, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        Authorization: `Bearer ${config.apiKey}`,
      },
      body: JSON.stringify(request.body),
      signal: controller.signal,
    });

    if (!res.ok) {
      const text = await res.text();
      throw new Error(`API ${res.status}: ${text.slice(0, 200)}`);
    }

    const contentType = (res.headers?.get?.("content-type") || "").toLowerCase();
    const raw = await res.text();
    if (
      config.provider === "openai" &&
      (contentType.includes("text/event-stream") || /^\s*(?:event|data):/m.test(raw))
    ) {
      return parseOpenAIEventStream(raw);
    }

    let data: any;
    try {
      data = JSON.parse(raw);
    } catch (error) {
      const detail = error instanceof Error ? error.message : String(error);
      throw new Error(`${config.provider} response is not valid JSON: ${detail}`);
    }
    return parseChatResponse(config.provider, data);
  } catch (error) {
    if (controller.signal.aborted) {
      throw new Error(`API request timed out after ${timeoutMs}ms`);
    }
    throw error;
  } finally {
    clearTimeout(timeout);
  }
}

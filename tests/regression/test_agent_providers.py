import json
import os
import unittest
from pathlib import Path
from subprocess import run


ROOT = Path(__file__).resolve().parents[2]


class AgentProviderTests(unittest.TestCase):
    def _run_node(self, script):
        env = os.environ.copy()
        # Provider tests must never inherit credentials or select a live API.
        for name in (
            "AGENT_PROVIDER",
            "AGENT_MODEL",
            "AGENT_BASE_URL",
            "DEEPSEEK_API_KEY",
            "DEEPSEEK_MODEL",
            "DEEPSEEK_BASE_URL",
            "OPENAI_API_KEY",
            "OPENAI_MODEL",
            "OPENAI_BASE_URL",
            "OPENAI_REASONING_EFFORT",
            "OPENAI_STRUCTURED_OUTPUT",
            "AGENT_REQUEST_TIMEOUT_MS",
        ):
            env.pop(name, None)
        completed = run(
            ["node", "-r", "ts-node/register", "-e", script],
            cwd=ROOT,
            env=env,
            capture_output=True,
            text=True,
            timeout=30,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        return json.loads(completed.stdout)

    def test_openai_config_and_request_use_responses_api(self):
        result = self._run_node(
            """
            const { buildChatRequest, resolveAgentConfig } = require('./agent/net');
            const config = resolveAgentConfig(
              { provider: 'openai' },
              {
                OPENAI_API_KEY: 'openai-key',
                OPENAI_MODEL: 'test-openai-model',
                OPENAI_BASE_URL: 'https://api.example.test/v1/',
              },
            );
            const request = buildChatRequest(config, {
              messages: [{ role: 'user', content: 'infer this' }],
            });
            console.log(JSON.stringify({ config, request }));
            """
        )

        self.assertEqual(result["config"]["provider"], "openai")
        self.assertEqual(result["config"]["apiKey"], "openai-key")
        self.assertEqual(result["config"]["model"], "test-openai-model")
        self.assertEqual(result["request"]["url"], "https://api.example.test/v1/responses")
        self.assertEqual(
            result["request"]["body"],
            {
                "model": "test-openai-model",
                "input": [{"role": "user", "content": "infer this"}],
            },
        )

    def test_openai_structured_output_uses_schema_and_fast_reasoning(self):
        result = self._run_node(
            """
            const { buildChatRequest } = require('./agent/net');
            const schema = {
              type: 'object',
              properties: {
                entries: { type: 'array', items: { type: 'string' } },
              },
              required: ['entries'],
              additionalProperties: false,
            };
            const request = buildChatRequest({
              provider: 'openai',
              apiKey: 'openai-key',
              model: 'gpt-5.6-sol',
              baseUrl: 'https://api.example.test/v1',
            }, {
              messages: [{ role: 'user', content: 'infer this' }],
              structuredOutput: { name: 'type_feedback', schema },
            });
            console.log(JSON.stringify(request.body));
            """
        )

        self.assertEqual(result["reasoning"], {"effort": "none"})
        self.assertEqual(
            result["text"]["format"],
            {
                "type": "json_schema",
                "name": "type_feedback",
                "strict": True,
                "schema": {
                    "type": "object",
                    "properties": {
                        "entries": {
                            "type": "array",
                            "items": {"type": "string"},
                        }
                    },
                    "required": ["entries"],
                    "additionalProperties": False,
                },
            },
        )

    def test_openai_pro_capabilities_do_not_receive_unsupported_defaults(self):
        result = self._run_node(
            """
            const { buildChatRequest } = require('./agent/net');
            const structuredOutput = {
              name: 'type_feedback',
              schema: {
                type: 'object',
                properties: {},
                required: [],
                additionalProperties: false,
              },
            };
            const make = model => buildChatRequest({
              provider: 'openai',
              apiKey: 'openai-key',
              model,
              baseUrl: 'https://api.example.test/v1',
            }, {
              messages: [{ role: 'user', content: 'infer this' }],
              structuredOutput,
            }).body;
            console.log(JSON.stringify({
              pro54: make('gpt-5.4-pro'),
              pro55: make('gpt-5.5-pro'),
            }));
            """
        )

        self.assertNotIn("reasoning", result["pro54"])
        self.assertNotIn("text", result["pro54"])
        self.assertNotIn("reasoning", result["pro55"])
        self.assertIn("text", result["pro55"])

    def test_openai_chat_sends_bearer_key_and_parses_output_text(self):
        result = self._run_node(
            """
            const { chat } = require('./agent/net');
            const config = {
              provider: 'openai',
              apiKey: 'secret-key',
              baseUrl: 'https://api.openai.com/v1',
              model: 'gpt-test',
            };
            let observed;
            const fakeFetch = async (url, init) => {
              observed = {
                url,
                method: init.method,
                authorization: init.headers.Authorization,
                body: JSON.parse(init.body),
              };
              const payload = {
                output: [
                  { type: 'reasoning', summary: [] },
                  {
                    type: 'message',
                    role: 'assistant',
                    content: [
                      { type: 'output_text', text: '[{"id":1,' },
                      { type: 'output_text', text: '"slot":"value","type":"number"}]' },
                    ],
                  },
                ],
              };
              return {
                ok: true,
                headers: { get: () => 'application/json' },
                text: async () => JSON.stringify(payload),
              };
            };
            chat(config, { messages: [{ role: 'user', content: 'prompt' }] }, fakeFetch)
              .then(message => console.log(JSON.stringify({ observed, message })))
              .catch(error => { console.error(error); process.exit(1); });
            """
        )

        self.assertEqual(result["observed"]["method"], "POST")
        self.assertEqual(result["observed"]["authorization"], "Bearer secret-key")
        self.assertNotIn("apiKey", result["observed"]["body"])
        self.assertEqual(
            result["message"]["content"],
            '[{"id":1,"slot":"value","type":"number"}]',
        )

    def test_openai_chat_parses_forced_sse_response(self):
        result = self._run_node(
            """
            const { chat } = require('./agent/net');
            const config = {
              provider: 'openai',
              apiKey: 'secret-key',
              baseUrl: 'https://api.openai.com/v1',
              model: 'gpt-test',
            };
            const event = (name, data) =>
              `event: ${name}\\r\\ndata: ${JSON.stringify(data)}\\r\\n\\r\\n`;
            const payload =
              event('response.created', { type: 'response.created' }) +
              event('response.output_text.delta', {
                type: 'response.output_text.delta',
                delta: '[{"id":1,',
              }) +
              event('response.output_text.delta', {
                type: 'response.output_text.delta',
                delta: '"slot":"value","type":"number"}]',
              }) +
              'event: response.completed\\r\\n' +
              'data: {\\r\\n' +
              'data: "type":"response.completed",\\r\\n' +
              'data: "response":{"status":"completed","output":[]}\\r\\n' +
              'data: }\\r\\n\\r\\n';
            const fakeFetch = async () => ({
              ok: true,
              headers: { get: () => 'text/event-stream; charset=utf-8' },
              text: async () => payload,
            });
            chat(config, { messages: [{ role: 'user', content: 'prompt' }] }, fakeFetch)
              .then(message => console.log(JSON.stringify(message)))
              .catch(error => { console.error(error); process.exit(1); });
            """
        )

        self.assertEqual(
            result["content"],
            '[{"id":1,"slot":"value","type":"number"}]',
        )

    def test_openai_sse_failure_and_truncation_raise_clear_errors(self):
        result = self._run_node(
            """
            const { parseOpenAIEventStream } = require('./agent/net');
            const event = (name, data) =>
              `event: ${name}\\ndata: ${JSON.stringify(data)}\\n\\n`;
            const errors = [];
            try {
              parseOpenAIEventStream(event('response.failed', {
                type: 'response.failed',
                response: { error: { message: 'upstream failed' } },
              }));
            } catch (error) {
              errors.push(error.message);
            }
            try {
              parseOpenAIEventStream(event('response.output_text.delta', {
                type: 'response.output_text.delta',
                delta: 'partial',
              }));
            } catch (error) {
              errors.push(error.message);
            }
            console.log(JSON.stringify(errors));
            """
        )

        self.assertIn("upstream failed", result[0])
        self.assertIn("before response.completed", result[1])

    def test_openai_sse_does_not_duplicate_authoritative_completed_text(self):
        result = self._run_node(
            """
            const { parseOpenAIEventStream } = require('./agent/net');
            const event = (name, data) =>
              `event: ${name}\\ndata: ${JSON.stringify(data)}\\n\\n`;
            const payload =
              event('response.output_text.delta', {
                type: 'response.output_text.delta',
                delta: 'complete text',
              }) +
              event('response.output_text.done', {
                type: 'response.output_text.done',
                text: 'complete text',
              }) +
              event('response.completed', {
                type: 'response.completed',
                response: {
                  status: 'completed',
                  output: [{
                    type: 'message',
                    content: [{ type: 'output_text', text: 'complete text' }],
                  }],
                },
              });
            console.log(JSON.stringify(parseOpenAIEventStream(payload)));
            """
        )

        self.assertEqual(result, {"content": "complete text"})

    def test_chat_timeout_covers_response_body(self):
        result = self._run_node(
            """
            const { chat } = require('./agent/net');
            const config = {
              provider: 'openai',
              apiKey: 'secret-key',
              baseUrl: 'https://api.openai.com/v1',
              model: 'gpt-test',
            };
            const fakeFetch = async (_url, init) => ({
              ok: true,
              headers: { get: () => 'text/event-stream' },
              text: () => new Promise((_resolve, reject) => {
                init.signal.addEventListener('abort', () => reject(new Error('aborted')));
              }),
            });
            chat(
              config,
              {
                messages: [{ role: 'user', content: 'prompt' }],
                timeoutMs: 10,
              },
              fakeFetch,
            )
              .then(() => { throw new Error('expected timeout'); })
              .catch(error => console.log(JSON.stringify({ error: error.message })));
            """
        )

        self.assertIn("timed out after 10ms", result["error"])

    def test_infer_does_not_retry_and_checkpoints_only_successful_batches(self):
        result = self._run_node(
            """
            const fs = require('fs');
            const os = require('os');
            const path = require('path');
            const net = require('./agent/net');
            net.setupProxy = async () => {};
            const attempts = { 1: 0, 2: 0 };
            net.chat = async (_config, options) => {
              const id = Number(options.messages[0].content.match(/id=(\\d+)/)[1]);
              attempts[id]++;
              if (id === 1) {
                throw new Error('OpenAI streaming response failed: Upstream request failed');
              }
              return { content: '[{"id":2,"slot":"value","type":"boolean"}]' };
            };
            const { inferTypes } = require('./agent/infer');
            const temporary = fs.mkdtempSync(path.join(os.tmpdir(), 'agent-no-retry-'));
            const source = path.join(temporary, 'index.ts');
            const output = path.join(temporary, 'inferinfo.json');
            fs.writeFileSync(source, 'let value;\\n');
            const originalLog = console.log;
            const originalError = console.error;
            const logs = [];
            const errors = [];
            console.log = (...args) => logs.push(args.join(' '));
            console.error = (...args) => errors.push(args.join(' '));
            console.warn = () => {};
            const spots = [1, 2].map(id => ({
              id,
              slot: 'value',
              file: source,
              relapath: 'index.ts',
              location: 0,
              context: 'value' + id,
              exprText: 'value' + id,
              exprKind: 'Identifier',
              morphKind: 'variable',
              pos: { line: id, column: 1 },
            }));
            inferTypes(spots, {
              provider: 'openai',
              apiKey: 'test-key',
              baseUrl: 'https://api.openai.com/v1',
              model: 'gpt-test',
            }, 1, undefined, 2, output).then(() => {
              console.log = originalLog;
              console.error = originalError;
              throw new Error('expected inference failure');
            }).catch(error => {
              console.log = originalLog;
              console.error = originalError;
              const checkpoint = JSON.parse(fs.readFileSync(output, 'utf8'));
              originalLog(JSON.stringify({
                attempts,
                error: error.message,
                logs,
                errors,
                checkpoint,
                temporaryExists: fs.readdirSync(temporary).some(name =>
                  name.startsWith('inferinfo.json.') && name.endsWith('.tmp')),
              }));
              fs.rmSync(temporary, { recursive: true, force: true });
            });
            """
        )

        self.assertEqual(result["attempts"], {"1": 1, "2": 1})
        self.assertIn("1 Agent batches failed", result["error"])
        self.assertTrue(
            any("共 2 个节点，分 1 个文件处理（并发 2）" in line
                for line in result["logs"])
        )
        self.assertTrue(any("批失败:" in line for line in result["errors"]))
        combined_logs = "\n".join(result["logs"] + result["errors"])
        for removed in ("批开始", "批完成", "尝试 1/", "重试", "每批最多尝试"):
            self.assertNotIn(removed, combined_logs)
        self.assertEqual(
            result["checkpoint"],
            [{"id": 2, "slot": "value", "type": "boolean"}],
        )
        self.assertFalse(result["temporaryExists"])

    def test_infer_parallelizes_batches_from_the_same_file(self):
        result = self._run_node(
            """
            const fs = require('fs');
            const os = require('os');
            const path = require('path');
            const net = require('./agent/net');
            net.setupProxy = async () => {};
            let active = 0;
            let peak = 0;
            net.chat = async (_config, options) => {
              const match = options.messages[0].content.match(/id=(\\d+)/);
              const id = Number(match[1]);
              active++;
              peak = Math.max(peak, active);
              await new Promise(resolve => setTimeout(resolve, 20));
              active--;
              return { content: JSON.stringify([{
                id,
                slot: 'value',
                type: 'number',
              }]) };
            };
            const { inferTypes } = require('./agent/infer');
            const temporary = fs.mkdtempSync(path.join(os.tmpdir(), 'agent-batches-'));
            const source = path.join(temporary, 'index.ts');
            fs.writeFileSync(source, 'let value;\\n');
            const spots = [1, 2, 3, 4].map(id => ({
              id,
              slot: 'value',
              file: source,
              relapath: 'index.ts',
              location: 0,
              context: 'value' + id,
              exprText: 'value' + id,
              exprKind: 'Identifier',
              morphKind: 'variable',
              pos: { line: id, column: 1 },
            }));
            const originalLog = console.log;
            console.log = () => {};
            inferTypes(spots, {
              provider: 'deepseek',
              apiKey: 'test-key',
              baseUrl: 'https://api.deepseek.com/v1',
              model: 'deepseek-chat',
            }, 1, undefined, 2).then(feedback => {
              console.log = originalLog;
              originalLog(JSON.stringify({ peak, count: feedback.length }));
              fs.rmSync(temporary, { recursive: true, force: true });
            }).catch(error => {
              console.log = originalLog;
              console.error(error);
              process.exit(1);
            });
            """
        )

        self.assertEqual(result["peak"], 2)
        self.assertEqual(result["count"], 4)

    def test_consensus_keeps_exact_agreements_and_drops_conflicts(self):
        result = self._run_node(
            """
            const fs = require('fs');
            const os = require('os');
            const path = require('path');
            const net = require('./agent/net');
            net.setupProxy = async () => {};
            let round = 0;
            net.chat = async () => {
              round++;
              return { content: JSON.stringify([
                { id: 1, slot: 'value', type: 'string' },
                { id: 2, slot: 'value', type: round === 1 ? 'number' : 'boolean' },
              ]) };
            };
            const { inferTypesConsensus } = require('./agent/infer');
            const temporary = fs.mkdtempSync(path.join(os.tmpdir(), 'agent-consensus-'));
            const source = path.join(temporary, 'index.ts');
            fs.writeFileSync(source, 'let first, second;\\n');
            const spots = [1, 2].map(id => ({
              id, slot: 'value', file: source, relapath: 'index.ts', location: 0,
              context: 'value' + id, exprText: 'value' + id,
              exprKind: 'Identifier', morphKind: 'variable',
              pos: { line: 1, column: id },
            }));
            const originalLog = console.log;
            console.log = () => {};
            inferTypesConsensus(spots, {
              provider: 'deepseek', apiKey: 'test-key',
              baseUrl: 'https://api.deepseek.com/v1', model: 'deepseek-chat',
            }, 2, 30, undefined, 1).then(feedback => {
              console.log = originalLog;
              originalLog(JSON.stringify(feedback));
              fs.rmSync(temporary, { recursive: true, force: true });
            }).catch(error => {
              console.log = originalLog;
              console.error(error);
              process.exit(1);
            });
            """
        )

        self.assertEqual(result, [{"id": 1, "slot": "value", "type": "string"}])

    def test_deepseek_defaults_and_response_shape_remain_compatible(self):
        result = self._run_node(
            """
            const {
              buildChatRequest,
              parseChatResponse,
              resolveAgentConfig,
            } = require('./agent/net');
            const config = resolveAgentConfig({}, { DEEPSEEK_API_KEY: 'deepseek-key' });
            const request = buildChatRequest(config, {
              messages: [{ role: 'user', content: 'prompt' }],
            });
            const message = parseChatResponse('deepseek', {
              choices: [{ message: { role: 'assistant', content: '[]' } }],
            });
            console.log(JSON.stringify({ config, request, message }));
            """
        )

        self.assertEqual(result["config"]["provider"], "deepseek")
        self.assertEqual(result["config"]["model"], "deepseek-chat")
        self.assertEqual(result["request"]["url"], "https://api.deepseek.com/v1/chat/completions")
        self.assertEqual(result["request"]["body"]["temperature"], 0)
        self.assertIn("messages", result["request"]["body"])
        self.assertEqual(result["message"], {"content": "[]"})

    def test_invalid_provider_and_missing_openai_text_fail_clearly(self):
        result = self._run_node(
            """
            const { parseChatResponse, resolveAgentConfig } = require('./agent/net');
            const errors = [];
            try {
              resolveAgentConfig({ provider: 'invalid' }, {});
            } catch (error) {
              errors.push(error.message);
            }
            try {
              parseChatResponse('openai', { output: [{ type: 'reasoning' }] });
            } catch (error) {
              errors.push(error.message);
            }
            const defaultOpenAI = resolveAgentConfig({ provider: 'openai' }, {});
            console.log(JSON.stringify({ errors, defaultOpenAI }));
            """
        )

        self.assertIn("expected deepseek or openai", result["errors"][0])
        self.assertIn("missing output_text", result["errors"][1])
        self.assertEqual(result["defaultOpenAI"]["model"], "gpt-4.1-mini")
        self.assertEqual(
            result["defaultOpenAI"]["baseUrl"],
            "https://api.openai.com/v1",
        )


if __name__ == "__main__":
    unittest.main()

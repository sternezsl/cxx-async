// cxx-async/examples/folly/src/folly_example.cpp
//
// An example showing how to interoperate with Folly.

#define FOLLY_HAS_COROUTINES 1

#include "folly_example.h"
#include <folly/CancellationToken.h>
#include <folly/Executor.h>
#include <folly/ScopeGuard.h>
#include <folly/Try.h>
#include <folly/Unit.h>
#include <folly/executors/CPUThreadPoolExecutor.h>
#include <folly/experimental/coro/BlockingWait.h>
#include <folly/experimental/coro/Task.h>
#include <folly/experimental/coro/ViaIfAsync.h>
#include <folly/experimental/coro/WithAsyncStack.h>
#include <folly/futures/Future-inl.h>
#include <folly/futures/Future.h>
#include <folly/futures/Promise-inl.h>
#include <folly/tracing/AsyncStack-inl.h>
#include <cstdlib>
#include <exception>
#include <experimental/coroutine>
#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>
#include "cxx-async-example-folly/src/main.rs.h"
#include "example.h"
#include "rust/cxx.h"
#include "rust/cxx_async.h"
#include "rust/cxx_async_folly.h"

CXXASYNC_DEFINE_FUTURE(RustFutureVoid, void);
CXXASYNC_DEFINE_FUTURE(RustFutureF64, double);
CXXASYNC_DEFINE_FUTURE(RustFutureString, rust::String);
CXXASYNC_DEFINE_FUTURE(foo::bar::RustFutureStringNamespaced, rust::String);
CXXASYNC_DEFINE_STREAM(RustStreamString, rust::String);

const size_t EXAMPLE_SPLIT_LIMIT = 32;
const size_t EXAMPLE_ARRAY_SIZE = 16384;

const size_t THREAD_COUNT = 8;

// TODO(pcwalton): It'd be nice to be able to spawn the extra threads that `dot_product` creates on
// a Rust thread pool instead. There has to be some kind of thread pool for this example to actually
// test parallelism, though.
folly::Executor::KeepAlive<folly::CPUThreadPoolExecutor> g_thread_pool(
    new folly::CPUThreadPoolExecutor(THREAD_COUNT));

// Multithreaded dot product computation.
static folly::coro::Task<double> do_dot_product_coro(const double a[],
                                                     const double b[],
                                                     size_t count) {
    if (count > EXAMPLE_SPLIT_LIMIT) {
        size_t half_count = count / 2;
        folly::Future<double> taskA =
            do_dot_product_coro(a, b, half_count).semi().via(g_thread_pool);
        folly::Future<double> taskB =
            do_dot_product_coro(a + half_count, b + half_count, count - half_count)
                .semi()
                .via(g_thread_pool);
        auto [first, second] = co_await folly::collectAll(std::move(taskA), std::move(taskB));
        co_return *first + *second;
    }

    double sum = 0.0;
    for (size_t i = 0; i < count; i++)
        sum += a[i] * b[i];
    co_return sum;
}

static folly::coro::Task<double> dot_product_coro() {
    Xorshift rand;
    std::vector<double> array_a, array_b;
    for (size_t i = 0; i < EXAMPLE_ARRAY_SIZE; i++) {
        array_a.push_back((double)rand.next());
        array_b.push_back((double)rand.next());
    }

    co_return co_await do_dot_product_coro(&array_a[0], &array_b[0], array_a.size());
}

// Multithreaded dot product computation, explicitly using Folly futures.
static folly::Future<double> do_dot_product_futures(const double a[],
                                                    const double b[],
                                                    size_t count) {
    if (count > EXAMPLE_SPLIT_LIMIT) {
        size_t half_count = count / 2;
        folly::Future<double> taskA = do_dot_product_futures(a, b, half_count);
        folly::Future<double> taskB =
            do_dot_product_futures(a + half_count, b + half_count, count - half_count);
        return folly::collectAll(std::move(taskA), std::move(taskB))
            .via(g_thread_pool)
            .thenValue([](auto&& results) {
                return std::get<0>(results).value() + std::get<1>(results).value();
            });
    }

    double sum = 0.0;
    for (size_t i = 0; i < count; i++)
        sum += a[i] * b[i];
    return folly::makeSemiFuture(std::move(sum)).via(g_thread_pool);
}

static folly::Future<double> dot_product_futures() {
    Xorshift rand;
    std::vector<double> array_a, array_b;
    for (size_t i = 0; i < EXAMPLE_ARRAY_SIZE; i++) {
        array_a.push_back((double)rand.next());
        array_b.push_back((double)rand.next());
    }

    return do_dot_product_futures(&array_a[0], &array_b[0], array_a.size());
}

static folly::coro::Task<double> not_product() {
    if (true)
        throw MyException("kaboom");
    co_return 1.0;  // Just to make this function a coroutine.
}

static folly::coro::Task<rust::String> ping_pong(int i) {
    std::string string(co_await rust_folly_ping_pong(i));
    co_return std::move(string) + "pong ";
}

rust::Box<RustFutureF64> folly_dot_product_coro() {
    co_return co_await dot_product_coro();
}

rust::Box<RustFutureF64> folly_dot_product_futures() {
    co_return co_await dot_product_futures();
}

rust::Box<foo::bar::RustFutureStringNamespaced> folly_get_namespaced_string() {
    co_await dot_product_coro();
    co_return rust::String("hello world");
}

double folly_call_rust_dot_product() {
    rust::Box<RustFutureF64> future = rust_dot_product();
    return folly::coro::blockingWait(std::move(future));
}

double folly_schedule_rust_dot_product() {
    rust::Box<RustFutureF64> future = rust_dot_product();
    return folly::coro::blockingWait(std::move(future));
}

rust::Box<RustFutureF64> folly_not_product() {
    co_return co_await not_product();
}

rust::String folly_call_rust_not_product() {
    try {
        rust::Box<RustFutureF64> oneshot_receiver = rust_not_product();
        folly::coro::blockingWait(std::move(oneshot_receiver));
        std::terminate();
    } catch (const std::exception& error) {
        return rust::String(error.what());
    }
}

rust::Box<RustFutureString> folly_ping_pong(int i) {
    co_return co_await ping_pong(i);
}

rust::Box<RustFutureVoid> folly_complete() {
    co_await dot_product_futures();     // Discard the result.
    co_return;
}

// Intentionally leak this to avoid annoying data race issues on thread destruction.
static Sem* g_dropped_future_sem;

static folly::coro::Task<double> folly_send_to_dropped_future_inner() {
    g_dropped_future_sem->wait();
    co_return 1.0;
}

void folly_send_to_dropped_future_go() {
    g_dropped_future_sem->signal();
}

rust::Box<RustFutureF64> folly_send_to_dropped_future() {
    g_dropped_future_sem = new Sem;
    co_return co_await folly_send_to_dropped_future_inner().semi().via(g_thread_pool);
}

rust::Box<RustStreamString> folly_fizzbuzz() {
    for (int i = 1; i <= 15; i++) {
        if (i % 15 == 0) {
            co_yield rust::String("FizzBuzz");
        } else if (i % 5 == 0) {
            co_yield rust::String("Buzz");
        } else if (i % 3 == 0) {
            co_yield rust::String("Fizz");
        } else {
            co_yield rust::String(std::to_string(i));
        }
    }
    co_return;
}

static folly::coro::Task<rust::String> fizzbuzz_inner(int i) {
    if (i % 15 == 0)
        co_return rust::String("FizzBuzz");
    if (i % 5 == 0)
        co_return rust::String("Buzz");
    if (i % 3 == 0)
        co_return rust::String("Fizz");
    co_return rust::String(std::to_string(i));
}

rust::Box<RustStreamString> folly_indirect_fizzbuzz() {
    for (int i = 1; i <= 15; i++)
        co_yield co_await fizzbuzz_inner(i).semi();
    co_return;
}

rust::Box<RustStreamString> folly_not_fizzbuzz() {
    for (int i = 1; i <= 10; i++)
        co_yield co_await fizzbuzz_inner(i);
    throw MyException("kablam");
}

import sqlite3
from time import time
import numpy as np
import torch
import redis
import wandb


class SQLiteEmbeddingsCache:
    """A cache that stores PyTorch tensors in a SQLite database.

    This cache provides persistent storage for tensors with efficient retrieval.
    Tensors are stored in binary format using torch's save/load functionality.
    """

    def __init__(self, db_path):
        """Initialize the cache with a SQLite database path.

        Args:
            db_path (str): Path to the SQLite database file
        """
        self.db_path = db_path
        self._init_db()

    def _get_connection(self):
        """Get a new database connection with proper settings.

        Yields:
            sqlite3.Connection: Database connection
        """
        return sqlite3.connect(self.db_path)

    def _init_db(self):
        """Initialize the SQLite database with required table."""
        with self._get_connection() as conn:
            conn.execute(
                """
                CREATE TABLE IF NOT EXISTS embeddings_cache (
                    key TEXT PRIMARY KEY,
                    array_data BLOB,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                )
            """
            )
            conn.execute("PRAGMA cache_size = 1000000")

    def __contains__(self, key):
        """Check if a key exists in the cache.

        Args:
            key: The key to check

        Returns:
            bool: True if key exists, False otherwise
        """
        with self._get_connection() as conn:
            cursor = conn.execute(
                "SELECT 1 FROM embeddings_cache WHERE key = ?", (key,)
            )
            return cursor.fetchone() is not None

    def __getitem__(self, key):
        """Retrieve a tensor from the cache.

        Args:
            key: The key to retrieve

        Returns:
            torch.Tensor: The stored tensor on the specified device

        Raises:
            KeyError: If key doesn't exist in cache
        """
        start = time()
        with self._get_connection() as conn:
            cursor = conn.execute(
                "SELECT array_data FROM embeddings_cache WHERE key = ?", (key,)
            )
            row = cursor.fetchone()
            if row is None:
                raise KeyError(key)

            # Load tensor from binary data
            tensor_bytes = row[0]
            result = torch.from_numpy(np.frombuffer(tensor_bytes, dtype=np.float32))

        wandb.log({"embedding_cache_get_time": time() - start})
        return result

    def __setitem__(self, key, value):
        """Store a tensor in the cache.

        Args:
            key: The key to store under
            value (torch.Tensor): The tensor to store
        """
        # Convert tensor to binary
        start = time()
        # Always save tensors from CPU to ensure compatibility
        tensor_bytes = value.cpu().numpy().tobytes()

        with self._get_connection() as conn:
            conn.execute(
                """
                INSERT OR REPLACE INTO embeddings_cache (key, array_data)
                VALUES (?, ?)
                """,
                (key, tensor_bytes),
            )
        wandb.log({"embedding_cache_set_time": time() - start})

    def get_many(self, keys):
        """Retrieve multiple tensors from the cache in a single transaction.

        Args:
            keys (list): List of keys to retrieve

        Returns:
            dict: Dictionary mapping keys to their corresponding tensors.
                 Only includes keys that were found in the cache.
        """
        start = time()
        placeholders = ",".join("?" * len(keys))

        with self._get_connection() as conn:
            cursor = conn.execute(
                f"SELECT key, array_data FROM embeddings_cache WHERE key IN ({placeholders})",
                keys,
            )

            result = {}
            for key, tensor_bytes in cursor:
                result[key] = torch.from_numpy(
                    np.frombuffer(tensor_bytes, dtype=np.float32)
                )

        wandb.log({"embedding_cache_get_time": time() - start})
        return result

    def set_many(self, tensors_dict):
        """Store multiple tensors in the cache in a single transaction.

        Args:
            tensors_dict (dict): Dictionary mapping keys to tensors
        """
        # Convert all tensors to binary format
        start = time()
        binary_data = []
        for key, tensor in tensors_dict.items():
            # Always save tensors from CPU to ensure compatibility
            tensor_bytes = tensor.cpu().numpy().tobytes()
            binary_data.append((key, tensor_bytes))

        with self._get_connection() as conn:
            conn.executemany(
                """
                INSERT OR REPLACE INTO embeddings_cache (key, array_data)
                VALUES (?, ?)
                """,
                binary_data,
            )

        wandb.log({"embedding_cache_set_time": time() - start})

    def get_batch(self, keys, missing_ok=False):
        """Retrieve a batch of tensors in the same order as the input keys.

        Args:
            keys (list): List of keys to retrieve
            missing_ok (bool): If True, missing keys will be skipped and None will be returned
                             in their place. If False, KeyError will be raised for missing keys.

        Returns:
            list: List of tensors in the same order as input keys.
                 Contains None for missing keys if missing_ok=True.

        Raises:
            KeyError: If any key is missing and missing_ok=False
        """
        result_dict = self.get_many(keys)

        result = []
        for key in keys:
            if key in result_dict:
                result.append(result_dict[key])
            elif missing_ok:
                result.append(None)
            else:
                raise KeyError(key)

        return result

    def clear(self):
        """Clear all entries from the cache."""
        with self._get_connection() as conn:
            conn.execute("DELETE FROM embeddings_cache")

    def delete(self, key):
        """Delete a specific key from the cache.

        Args:
            key: The key to delete
        """
        with self._get_connection() as conn:
            conn.execute("DELETE FROM embeddings_cache WHERE key = ?", (key,))

    def delete_many(self, keys):
        """Delete multiple keys from the cache in a single transaction.

        Args:
            keys (list): List of keys to delete
        """
        placeholders = ",".join("?" * len(keys))

        with self._get_connection() as conn:
            conn.execute(
                f"DELETE FROM embeddings_cache WHERE key IN ({placeholders})", keys
            )

    def get_all_keys(self):
        """Get all keys in the cache.

        Returns:
            list: List of all keys in the cache
        """
        with self._get_connection() as conn:
            cursor = conn.execute("SELECT key FROM embeddings_cache")
            return [row[0] for row in cursor.fetchall()]

    def get_size(self):
        """Get the number of entries in the cache.

        Returns:
            int: Number of entries in the cache
        """
        with self._get_connection() as conn:
            cursor = conn.execute("SELECT COUNT(*) FROM embeddings_cache")
            return cursor.fetchone()[0]


class RedisEmbeddingsCache:
    """A cache that stores PyTorch tensors in a Redis database.

    This cache provides persistent storage for tensors with efficient retrieval.
    Tensors are stored in binary format using torch's save/load functionality.
    """

    def __init__(self, redis_db):
        """Initialize the cache with a Redis database.

        Args:
            redis_db (int): The Redis database to use
        """
        self._conn = redis.Redis(host="localhost", port=6379, db=redis_db)

    def __del__(self):
        """Cleanup database connection on object deletion."""
        if self._conn is not None:
            try:
                self._conn.close()
            except Exception:
                pass
            self._conn = None

    def __contains__(self, key):
        """Check if a key exists in the cache.

        Args:
            key: The key to check

        Returns:
            bool: True if key exists, False otherwise
        """

        return self._conn.hexists("embeddings_cache", key)

    def __getitem__(self, key):
        """Retrieve a tensor from the cache.

        Args:
            key: The key to retrieve

        Returns:
            torch.Tensor: The stored tensor on the specified device

        Raises:
            KeyError: If key doesn't exist in cache
        """
        start = time()
        tensor_bytes = self._conn.hget("embeddings_cache", key)
        if tensor_bytes is None:
            raise KeyError(key)

        # Load tensor from binary data
        result = torch.from_numpy(np.frombuffer(tensor_bytes, dtype=np.float32))

        wandb.log({"embedding_cache_get_time": time() - start})
        return result

    def __setitem__(self, key, value):
        """Store a tensor in the cache.

        Args:
            key: The key to store under
            value (torch.Tensor): The tensor to store
        """
        # Convert tensor to binary
        start = time()
        # Always save tensors from CPU to ensure compatibility
        tensor_bytes = value.cpu().numpy().tobytes()

        self._conn.hset("embeddings_cache", key, tensor_bytes)
        wandb.log({"embedding_cache_set_time": time() - start})

    def get_batch(self, keys):
        """Retrieve multiple tensors from the cache in a single transaction.

        Args:
            keys (list): List of keys to retrieve

        Returns:
            dict: Dictionary mapping keys to their corresponding tensors.
                 Only includes keys that were found in the cache.
        """
        start = time()
        result = self._conn.hmget("embeddings_cache", keys)
        result = [
            torch.from_numpy(np.frombuffer(tensor_bytes, dtype=np.float32))
            for tensor_bytes in result
        ]

        wandb.log({"embedding_cache_get_time": time() - start})
        return result

    def set_many(self, tensors_dict):
        """Store multiple tensors in the cache in a single transaction.

        Args:
            tensors_dict (dict): Dictionary mapping keys to tensors
        """
        # Convert all tensors to binary format
        start = time()
        binary_data = {
            key: tensor.cpu().numpy().tobytes() for key, tensor in tensors_dict.items()
        }

        self._conn.hmset("embeddings_cache", binary_data)

        wandb.log({"embedding_cache_set_time": time() - start})

    def clear(self):
        """Clear all entries from the cache."""
        self._conn.delete("embeddings_cache")

    def delete(self, key):
        """Delete a specific key from the cache.

        Args:
            key: The key to delete
        """
        self._conn.hdel("embeddings_cache", key)

    def delete_many(self, keys):
        """Delete multiple keys from the cache in a single transaction.

        Args:
            keys (list): List of keys to delete
        """

        self._conn.hdel("embeddings_cache", *keys)

    def get_all_keys(self):
        """Get all keys in the cache.

        Returns:
            list: List of all keys in the cache
        """
        return self._conn.hkeys("embeddings_cache")

    def get_size(self):
        """Get the number of entries in the cache.

        Returns:
            int: Number of entries in the cache
        """
        return self._conn.hlen("embeddings_cache")
